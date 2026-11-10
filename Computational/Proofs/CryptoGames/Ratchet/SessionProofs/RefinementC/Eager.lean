/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Eager mirror of the C side and the initial invariant

Relates the H1 game with `libsignalToModularSchemeSim`, `simCNoneWinEvent`, `hiddenSaltGame`, and
ambiguous stopping runs to `runSimCEager` from the initial joint state, and establishes the initial
invariant `simInvCX_init`.
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

private def c1a_simStepImplCNone (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) :
    QueryImpl (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (JointC PQ Pt ℓ) ProbComp) :=
  fun q => StateT.mk fun x => stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x

private def c1a_runSimCNone {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) :
    ProbComp (α × JointC PQ Pt ℓ) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (JointC PQ Pt ℓ) ProbComp) +
    c1a_simStepImplCNone P ℓ Dh encPt encT decT idOf lam qep
  (simulateQ impl oa).run x

private theorem c1a_runSimCNone_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (a : α) (x : JointC PQ Pt ℓ) :
    c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep (pure a) x = pure (a, x) := by
  simp [c1a_runSimCNone]

private theorem c1a_runSimCNone_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) :
    c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont) x =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep (cont y) x := by
  simp only [c1a_runSimCNone, simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, StateT.run_bind]
  have h1 :
      (liftM ((QueryImpl.liftTarget (StateT (JointC PQ Pt ℓ) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) +
        c1a_simStepImplCNone P ℓ Dh encPt encT decT idOf lam qep) (.inl u)) :
        StateT _ ProbComp (unifSpec.Range u)).run x =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y => pure (y, x)) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

private theorem c1a_runSimCNone_inr_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) :
    c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont) x =
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x >>= fun r =>
        c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep (cont r.1) r.2 := by
  simp only [c1a_runSimCNone, c1a_simStepImplCNone, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  rfl

private theorem c1a_idHook_lift {α : Type} (x : Fig8Comp Pt ℓ α) :
    (idHook (ℓ := ℓ)).lift x = x := rfl

private theorem c1a_idHook_probe_run (Q : Party) (c : Fig8C Pt) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (StateT.lift ((idHook (ℓ := ℓ)).probe Q c) :
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) Unit).run sC = pure ((), sC) := rfl

private theorem c1a_probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift x).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) x).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

private theorem c1a_probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem c1a_run_h1_eq
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (b : Bool) (A : SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    SM.run fig (2 + 1) qepF SM.Config.h1 b A = (do
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      (simulateQ (fig8ImplH1 fig qepF) A).run (SM.initState fig k b)) := rfl

private theorem c1a_simImplC_probeHook_inl_run
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (u : unifSpec.Domain) (x : JointC PQ Pt ℓ) :
    (((simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
        (fs := fs) (H := probeHook fig qepF) Dh (.inl u)).run x.1).run x.2) =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
        fun y => pure ((y, x.1), x.2)) := by
  change (((StateT.lift ((probeHook fig qepF).lift
    (OracleSpec.query (spec := unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl u))) : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) _).run x.1).run x.2) = _
  simp only [StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply, StateT.run_bind,
    c1a_probeHook_lift_run, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, bind_assoc, pure_bind, StateT.run_pure]
  have h1 : (fig8ImplH1 fig qepF (.inl u)).run x.2.1 =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
        fun y => pure (y, x.2.1)) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

private theorem c1a_simulateQ_probeHook_eq_runSimCNone {α : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    (((simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
        (fs := fs) (H := probeHook fig (qep + 1)) Dh) oa).run x.1).run x.2 >>=
      fun r => pure (r.1.1, (r.1.2, r.2))) =
      c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep oa x := by
  intro fig fs
  induction oa using OracleComp.inductionOn generalizing x with
  | pure a =>
    simp [c1a_runSimCNone_pure]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        simulateQ_query_bind, StateT.run_bind, bind_assoc, c1a_runSimCNone_inl_bind]
      have h1 := c1a_simImplC_probeHook_inl_run P encT decT qep fig fs (qep + 1) Dh u x
      change (((simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
        (fs := fs) (H := probeHook fig (qep + 1)) Dh (.inl u)).run x.1).run x.2 >>= _) = _
      rw [h1]
      simp only [bind_assoc, pure_bind]
      congr 1; funext y
      exact ih y x
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        simulateQ_query_bind, StateT.run_bind, bind_assoc, c1a_runSimCNone_inr_bind]
      unfold stepSimCNone
      simp only [bind_assoc, pure_bind]
      congr 1; funext r
      exact ih r.1.1 (r.1.2, r.2)

private theorem c1a_hiddenSaltGame_eq_runSimCNone (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    hiddenSaltGame P ℓ Dh encPt encT decT idOf lam qep A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
              (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k b, false) >>= fun z =>
              pure z.2.2.2) := by
  intro sm
  unfold hiddenSaltGame simRunCWith
  congr 1; funext b
  congr 1; funext k
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply,
    StateT.run_bind, StateT.run_pure, c1a_probeHook_lift_run, bind_assoc, pure_bind]
  have h1 : (simulateQ (fig8ImplH1 sm (qep + 1))
      (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))).run
      (SM.initState sm k b) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqrKey =>
        pure (pqrKey, SM.initState sm k b)) := by
    unfold fig8ImplH1
    rw [Construction.AuthL11.simulateQ_liftM_run]
  change (do
      let p ← (simulateQ (fig8ImplH1 sm (qep + 1)) (liftM ($ᵗ BitVec 256))).run (SM.initState sm k b)
      let x ← (((simulateQ (simImplC P encT decT qep sm (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook sm (qep + 1)) Dh) A).run
        (initSimC (P.spqr.init .a2b p.1) (P.spqr.init .b2a p.1))).run (p.2, false))
      pure x.2.2) = _
  rw [h1]
  simp only [bind_assoc, pure_bind]
  congr 1; funext pqrKey
  rw [← c1a_simulateQ_probeHook_eq_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm k b, false)]
  simp only [bind_assoc, pure_bind]
  rfl

private def c1a_rel {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    (mId : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (simulateQ (fig8ImplH1 fig qepF) (mId.run sC)).run gh.1 =
      ((mPr.run sC).run gh >>= fun r => pure (r.1, r.2.1))

private theorem c1a_rel_pure {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (a : α) :
    c1a_rel (PQ := PQ) fig qepF (pure a) (pure a) := by
  intro sC gh
  simp

private theorem c1a_rel_bind {α β : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ}
    {mId : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {kId : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β}
    {kPr : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : c1a_rel fig qepF mId mPr)
    (hk : ∀ a, c1a_rel fig qepF (kId a) (kPr a)) :
    c1a_rel fig qepF (mId >>= kId) (mPr >>= kPr) := by
  intro sC gh
  simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
  rw [hm sC gh]
  simp only [bind_assoc, pure_bind]
  congr 1; funext r
  exact hk r.1.1 r.1.2 r.2

private theorem c1a_rel_get
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) :
    c1a_rel (PQ := PQ) fig qepF
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ))
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ)) := by
  intro sC gh
  simp

private theorem c1a_rel_set
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    c1a_rel (PQ := PQ) fig qepF
      (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit)
      (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) PUnit) := by
  intro sC gh
  simp

private theorem c1a_rel_modify
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    c1a_rel (PQ := PQ) fig qepF
      (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit)
      (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) PUnit) := by
  intro sC gh
  simp

private theorem c1a_rel_ite {α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {P_cond : Prop} [Decidable P_cond]
    {tId eId : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {tPr ePr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : c1a_rel fig qepF tId tPr) (he : c1a_rel fig qepF eId ePr) :
    c1a_rel fig qepF (if P_cond then tId else eId) (if P_cond then tPr else ePr) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem c1a_zoomB_probeHook_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((runOnBaseState (probeHook fig qepF) x).run sC).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1 >>= fun r =>
        pure ((r.1.1, { sC with base := r.1.2 }), (r.2, gh.2))) := by
  change (((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh = _
  rw [StateT.run_bind, c1a_probeHook_lift_run]
  simp only [bind_assoc, pure_bind, StateT.run_pure]

private theorem c1a_rel_zoomB {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    c1a_rel (PQ := PQ) fig qepF (runOnBaseState idHook x) (runOnBaseState (probeHook fig qepF) x) := by
  intro sC gh
  change (simulateQ (fig8ImplH1 fig qepF)
      (idHook.lift (x.run sC.base) >>= fun p => pure (p.1, { sC with base := p.2 }))).run gh.1 =
    (((runOnBaseState (probeHook fig qepF) x).run sC).run gh >>= fun r => pure (r.1, r.2.1))
  rw [c1a_zoomB_probeHook_run]
  simp only [c1a_idHook_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind]

private theorem c1a_rel_liftC {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    c1a_rel (PQ := PQ) fig qepF
      (LibsignalSimC.liftC idHook x) (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh
  unfold LibsignalSimC.liftC
  simp only [StateT.run_lift, c1a_idHook_lift, map_eq_bind_pure_comp, Function.comp_apply,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, c1a_probeHook_lift_run,
    bind_assoc, pure_bind]

private theorem c1a_rel_probe
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1a_rel (PQ := PQ) fig qepF
      (StateT.lift (idHook.probe Q c'))
      (StateT.lift ((probeHook fig qepF).probe Q c')) := by
  intro sC gh
  rw [c1a_idHook_probe_run]
  simp only [simulateQ_pure, StateT.run_pure, StateT.run_lift, map_eq_bind_pure_comp,
    Function.comp_apply, StateT.run_bind, c1a_probeHook_probe_run, pure_bind]

private theorem c1a_rel_guardC {α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ}
    {mId : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : c1a_rel fig qepF mId mPr) :
    c1a_rel fig qepF (guardC mId) (guardC mPr) := by
  unfold guardC
  refine c1a_rel_bind (c1a_rel_get fig qepF) fun sC => ?_
  exact c1a_rel_ite (c1a_rel_pure fig qepF none) hm

private theorem c1a_rel_simSendC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    c1a_rel fig qepF
      (simSendC P qep fig idHook Q m₀ chal r)
      (simSendC P qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendC
  refine c1a_rel_bind (c1a_rel_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact c1a_rel_pure fig qepF none
  | some w =>
    refine c1a_rel_bind (c1a_rel_get fig qepF) fun sC => ?_
    exact c1a_rel_bind (c1a_rel_set fig qepF _) fun _ => c1a_rel_pure fig qepF (some w)

private theorem c1a_rel_fwdAnswerC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    c1a_rel fig qepF
      (fwdAnswerC qep fig fs idHook Q w isDel ci? T pq' c')
      (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine c1a_rel_bind (c1a_rel_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact c1a_rel_zoomB (PQ := PQ) fig qepF _
  | some r =>
    cases r <;>
      first
      | exact c1a_rel_zoomB (PQ := PQ) fig qepF _
      | exact c1a_rel_bind (c1a_rel_modify fig qepF _) fun _ =>
          c1a_rel_zoomB (PQ := PQ) fig qepF _

private theorem c1a_rel_resyncC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    c1a_rel fig qepF
      (resyncC qep fig fs idHook Q w ci? T pq' c r)
      (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact c1a_rel_pure fig qepF _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine c1a_rel_bind (c1a_rel_liftC fig qepF _) fun res => ?_
    cases res with
    | none => exact c1a_rel_pure fig qepF _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact c1a_rel_bind (c1a_rel_modify fig qepF _) fun _ =>
          c1a_rel_zoomB (PQ := PQ) fig qepF _
      | _ => exact c1a_rel_pure fig qepF _

private theorem c1a_rel_fwdC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    c1a_rel fig qepF
      (fwdC P qep fig fs idHook Q w isDel ci? T pq' honestC c')
      (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine c1a_rel_bind (c1a_rel_get fig qepF) fun sC => ?_
  cases honestC with
  | none => exact c1a_rel_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    refine c1a_rel_ite ?_ (c1a_rel_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact c1a_rel_resyncC qep fig fs qepF Q w ci? T pq' c r
    | none =>
      exact c1a_rel_bind (c1a_rel_probe fig qepF Q c') fun _ =>
        c1a_rel_pure fig qepF _

private theorem c1a_rel_fwdEvictC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    c1a_rel fig qepF
      (fwdEvictC qep fig fs idHook Q w isDel T pq' c')
      (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine c1a_rel_bind (c1a_rel_get fig qepF) fun sC => ?_
  refine c1a_rel_ite ?_ (c1a_rel_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c')
  exact c1a_rel_bind (c1a_rel_probe fig qepF Q c') fun _ => c1a_rel_pure fig qepF _

private theorem c1a_rel_simRecvC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    c1a_rel fig qepF
      (simRecvC P encT decT qep fig fs idHook Q w isDel)
      (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine c1a_rel_bind (c1a_rel_get fig qepF) fun sC => ?_
  dsimp only
  refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
  refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
  refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
  refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact c1a_rel_pure fig qepF _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
    refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact c1a_rel_pure fig qepF _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
        exact c1a_rel_fwdC P qep fig fs qepF Q w isDel (some ci) h.senderRatchetKey pq' _ _
      | none =>
        dsimp only
        refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
        refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
        refine c1a_rel_ite
          (c1a_rel_bind (c1a_rel_modify fig qepF _) fun _ => ?_) ?_ <;>
        · refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
          cases decT h.senderRatchetKey with
          | none => exact c1a_rel_pure fig qepF _
          | some T =>
            exact c1a_rel_ite
              (c1a_rel_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (c1a_rel_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)

private theorem c1a_rel_simCorrC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    c1a_rel fig qepF
      (simCorrC P encT idHook Dh Q)
      (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine c1a_rel_bind (c1a_rel_get fig qepF) fun sC => ?_
  refine c1a_rel_ite (c1a_rel_pure fig qepF _) ?_
  refine c1a_rel_bind (c1a_rel_liftC fig qepF _) fun res => ?_
  cases res with
  | none => exact c1a_rel_pure fig qepF _
  | some st =>
    exact c1a_rel_bind (c1a_rel_set fig qepF _) fun _ => c1a_rel_pure fig qepF _

private theorem c1a_rel_simImplC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    c1a_rel fig qepF
      (simImplC P encT decT qep fig fs idHook Dh t)
      (simImplC P encT decT qep fig fs (probeHook fig qepF) Dh t) := by
  rcases t with u | ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact c1a_rel_liftC fig qepF _
  · exact c1a_rel_guardC (c1a_rel_simSendC P qep fig qepF Q m₀ none r')
  · exact c1a_rel_guardC (c1a_rel_simSendC P qep fig qepF Q m₀ (some m₁) r')
  · exact c1a_rel_guardC (c1a_rel_simRecvC P encT decT qep fig fs qepF Q w true)
  · exact c1a_rel_guardC (c1a_rel_simRecvC P encT decT qep fig fs qepF Q w false)
  · exact c1a_rel_guardC (c1a_rel_simCorrC P encT fig qepF Dh Q)

private theorem c1a_rel_simulateQ {α : Type} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α) :
    c1a_rel fig qepF
      (simulateQ (simImplC P encT decT qep fig fs idHook Dh) oa)
      (simulateQ (simImplC P encT decT qep fig fs (probeHook fig qepF) Dh) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [simulateQ_pure]
    exact c1a_rel_pure fig qepF a
  | query_bind t cont ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    exact c1a_rel_bind (c1a_rel_simImplC P encT decT qep fig fs qepF Dh t) fun a => ih a

private theorem c1a_game_simRunC_none_eq_runSimCNone (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    SM.game sm (2 + 1) (qep + 1) SM.Config.h1 (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
              (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k b, false) >>= fun z =>
               pure (b == z.1 || z.2.2.1.win)) := by
  intro sm
  unfold SM.game Refine.libsignalToModularSchemeSim runLibsignalToModularSchemeSim simRunCWith
  congr 1; funext b
  rw [c1a_run_h1_eq]
  simp only [bind_assoc]
  congr 1; funext k
  simp only [c1a_idHook_lift, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply,
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
        ((simulateQ (simImplC P encT decT qep sm (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh) A).run
          (initSimC (P.spqr.init .a2b x.1) (P.spqr.init .b2a x.1)))).run x.2
      pure (b == x.1.1 || x.2.win)) = _
  rw [h1]
  simp only [bind_assoc, pure_bind]
  congr 1; funext pqrKey
  have hrel := c1a_rel_simulateQ P encT decT qep sm (lFS P.C P.codec ℓ encT idOf 25000)
    (qep + 1) Dh A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (SM.initState sm k b, false)
  rw [← c1a_simulateQ_probeHook_eq_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm k b, false)]
  change (simulateQ (fig8ImplH1 sm (qep + 1))
      ((simulateQ (simImplC P encT decT qep sm (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))).run
      (SM.initState sm k b, false).1 >>= _ = _
  rw [hrel]
  simp only [bind_assoc, pure_bind]
  rfl

private theorem c1a_cxSend_base (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q sC s' res).base = s' := by
  cases res <;> rfl

private theorem c1a_stepSimCNone_send_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rc : Option PQC)
    (x : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (((guardC (simSendC (P := P) (qep := qep) (fig := fig) (H := probeHook fig (qep + 1))
        Q m₀ chal rc)).run x.1).run x.2) >>=
      (fun r => pure (r.1.1, (r.1.2, r.2))) =
    ((simulateQ (fig8ImplH1 fig (qep + 1))
        ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal rc)).run x.1.base)).run x.2.1 >>=
      fun r => pure (r.1.1, (r.1.2, r.2))) >>= fun res =>
      pure (res.1, (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2)) := by
  intro fig
  unfold guardC LibsignalSim.guard simSendC
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : x.1.base.stopped
  · simp [hstop, cxSend]
  · simp only [hstop, Bool.false_eq_true, ite_false, StateT.run_bind,
      c1a_zoomB_probeHook_run, bind_assoc, pure_bind]
    congr 1; funext r
    cases r1 : r.1.1 <;>
      (simp [r1, cxSend, fig, StateT.run_get, StateT.run_set, StateT.run_bind, StateT.run_pure]; try rfl)

private theorem c1a_stepSimCNone_transmit_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (rc : Option PQC) (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inl (Q, m₀, rc))))) x =
      stepSim P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inl (.inl (Q, m₀, rc))))) x.sim >>=
        fun res => pure (res.1, (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2)) := by
  simpa [stepSimCNone, simImplC, stepSim, stepSimNone, LibsignalSim.simImpl, fig8ImplH1, JointC.sim]
    using c1a_stepSimCNone_send_eq P ℓ Dh encPt encT idOf lam qep Q m₀ none rc x

private theorem c1a_stepSimCNone_chall_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (rc : Option PQC) (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))) x =
      stepSim P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))) x.sim >>=
        fun res => pure (res.1, (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2)) := by
  simpa [stepSimCNone, simImplC, stepSim, stepSimNone, LibsignalSim.simImpl, fig8ImplH1, JointC.sim]
    using c1a_stepSimCNone_send_eq P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) rc x

private theorem c1a_simRecvUsesCoin_none (P : Params PQ PQC)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvUsesCoin P encT decT none Q w isDel st = false := by
  unfold simRecvUsesCoin
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only
  simp only [hnone, Bool.and_false, Bool.false_eq_true, ite_false]
  repeat' (first | rfl | split)

private theorem c1a_onAcceptPure_stopped (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.stopped = s.stopped := by
  unfold onAcceptPure
  dsimp only
  repeat' (first | rfl | split)

private theorem c1a_onAnswerPure_stopped (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped := by
  unfold onAnswerPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm => exact c1a_onAcceptPure_stopped qep Q w isDel t i _ ci? T pq' s

private theorem c1a_simRecvStep_none_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
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
              by_cases h6 : (!addressCheckPasses h.addresses (P.expectedAddrs Q)) = true
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
                    · simp only [h7, Bool.false_eq_true, ↓reduceIte, c1a_onAnswerPure_stopped]; simp [h1]
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
                            simp only [Bool.false_eq_true, ↓reduceIte, c1a_onAnswerPure_stopped]
                            by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]

private theorem c1a_simRecvStops_none (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w isDel st = false := by
  unfold simRecvStops
  rw [c1a_simRecvStep_none_stopped]
  cases st.1.stopped <;> simp

private theorem c1a_stepSimC_none_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) :
    stepSimC P ℓ Dh encPt encT decT idOf lam qep none q x =
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSimC, c1a_simRecvStops_none]

private theorem c1a_evalDist_stepSimCEagerTransmit_none (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (rc : Option PQC)
    (x : JointC PQ Pt ℓ)
    (G : Option (List (BitVec 8)) → JointC PQ Pt ℓ → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (x.1.base.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep none Q m₀ rc x ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inl (Q, m₀, rc))))) x >>= fun r =>
        withEagerCoins r.2.1.base.mir (G r.1 r.2)] := by
  unfold stepSimCEagerTransmit
  simp only [bind_assoc, pure_bind]
  have h1 := evalDist_stepSimEagerTransmitW P Inv ℓ Dh encPt encT decT idOf lam qep none Q m₀ rc x.sim
    (fun ans st' ec' => G ans (cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2) ec')
    hpq hW0
  change 𝒟[withEagerCoins x.sim.1.mir (fun ec =>
      stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep none Q m₀ rc x.sim ec >>= fun res =>
      G res.1 (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1.1 res.1, res.2.1.2, x.2.2) res.2.2)] = _
  rw [h1, c1a_stepSimCNone_transmit_eq]
  simp only [bind_assoc, pure_bind, c1a_cxSend_base]

private theorem c1a_evalDist_stepSimCEagerChall_none (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (rc : Option PQC)
    (x : JointC PQ Pt ℓ)
    (G : Option (List (BitVec 8)) → JointC PQ Pt ℓ → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (x.1.base.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep none Q m₀ m₁ rc x ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))) x >>= fun r =>
        withEagerCoins r.2.1.base.mir (G r.1 r.2)] := by
  unfold stepSimCEagerChall
  simp only [bind_assoc, pure_bind]
  have h1 := evalDist_stepSimEagerChallW P Inv ℓ Dh encPt encT decT idOf lam qep none Q m₀ m₁ rc x.sim
    (fun ans st' ec' => G ans (cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2) ec')
    hpq hW0
  change 𝒟[withEagerCoins x.sim.1.mir (fun ec =>
      stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep none Q m₀ m₁ rc x.sim ec >>= fun res =>
      G res.1 (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1.1 res.1, res.2.1.2, x.2.2) res.2.2)] = _
  rw [h1, c1a_stepSimCNone_chall_eq]
  simp only [bind_assoc, pure_bind, c1a_cxSend_base]

private theorem c1a_evalDist_stepSimCEager_none (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ)
    (G : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      JointC PQ Pt ℓ → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (x.1.base.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q x ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x >>= fun r =>
        withEagerCoins r.2.1.base.mir (G r.1 r.2)] := by
  rcases q with ((((⟨Q, m₀, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact c1a_evalDist_stepSimCEagerTransmit_none P Inv ℓ Dh encPt encT decT idOf lam qep Q m₀ rc x G hpq hW0
  · exact c1a_evalDist_stepSimCEagerChall_none P Inv ℓ Dh encPt encT decT idOf lam qep Q m₀ m₁ rc x G hpq hW0
  · simp only [stepSimCEager, stepSimCEagerDeliver, c1a_simRecvUsesCoin_none, Bool.false_and, Bool.false_eq_true,
      ite_false, evictStopsC_none, c1a_stepSimC_none_eq, bind_assoc, pure_bind]
    exact evalDist_withEagerCoins_step_unused x.1.base.mir
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x)
      (fun res => res.2.1.base.mir) (fun res => G res.1 res.2)
  · simp only [stepSimCEager, stepSimCEagerInject, c1a_simRecvUsesCoin_none, Bool.false_and, Bool.false_eq_true,
      ite_false, evictStopsC_none, c1a_stepSimC_none_eq, bind_assoc, pure_bind]
    exact evalDist_withEagerCoins_step_unused x.1.base.mir
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x)
      (fun res => res.2.1.base.mir) (fun res => G res.1 res.2)
  · simp only [stepSimCEager, stepSimCEagerCorr, c1a_stepSimC_none_eq, bind_assoc, pure_bind]
    exact evalDist_withEagerCoins_step_unused x.1.base.mir
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x)
      (fun res => res.2.1.base.mir) (fun res => G res.1 res.2)

private theorem c1a_pq_update_inv {PQ : Type} {Inv : PQ → Prop} {pq : Party → PQ} {Q : Party} {pq' : PQ}
    (hpq : ∀ R, Inv (pq R)) (hpq' : Inv pq') :
    ∀ R, Inv (Function.update pq Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa using hpq'
  · simpa [Function.update_of_ne hR] using hpq R

private theorem c1a_onAcceptPure_pqInv (Inv : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv (s.pq R)) (hpq' : Inv pq') :
    ∀ R, Inv ((onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq R) := by
  have hupd : ∀ R, Inv (Function.update s.pq Q pq' R) := c1a_pq_update_inv hpq hpq'
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit Q.other w with
    | none => exact hpq
    | some _ => exact hupd
  · split
    · exact hpq
    · split
      · exact hupd
      · exact hpq

private theorem c1a_onAnswerPure_pqInv (Inv : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv (s.pq R)) (hpq' : Inv pq') :
    ∀ R, Inv ((onAnswerPure qep Q w isDel ci? T pq' res s).2.pq R) := by
  unfold onAnswerPure
  cases res with
  | none => exact hpq
  | some r =>
    cases r with
    | rejected => exact hpq
    | accepted t i pm =>
      exact c1a_onAcceptPure_pqInv Inv qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s hpq hpq'

private def c1a_pres_pq {α : Type} (Inv : PQ → Prop)
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (∀ R, Inv (sC.base.pq R)) →
    ∀ r ∈ support ((m.run sC).run gh), ∀ R, Inv (r.1.2.base.pq R)

private theorem c1a_pres_pq_pure {α : Type} (Inv : PQ → Prop) (a : α) :
    c1a_pres_pq (Pt := Pt) (ℓ := ℓ) Inv (pure a) := by
  intro sC gh hpq r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1a_pres_pq_bind {α β : Type} {Inv : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : c1a_pres_pq Inv m) (hk : ∀ a, c1a_pres_pq Inv (k a)) :
    c1a_pres_pq Inv (m >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  exact hk r₁.1.1 r₁.1.2 r₁.2 (hm sC gh hpq r₁ hr₁) r hr

private theorem c1a_pres_pq_get (Inv : PQ → Prop) :
    c1a_pres_pq (Pt := Pt) (ℓ := ℓ) Inv get := by
  intro sC gh hpq r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1a_pres_pq_ite {α : Type} {Inv : PQ → Prop} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : c1a_pres_pq Inv t) (he : c1a_pres_pq Inv e) :
    c1a_pres_pq Inv (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem c1a_pres_pq_liftC {α : Type} (Inv : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    c1a_pres_pq Inv (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift x >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1a_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨_, _, rfl⟩
  exact hpq

private theorem c1a_pres_pq_probe (Inv : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1a_pres_pq Inv
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1a_probeHook_probe_run] at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1a_pres_pq_modify_kept (Inv : PQ → Prop)
    (f : (Party → Kept Pt) → (Party → Kept Pt)) :
    c1a_pres_pq (Pt := Pt) (ℓ := ℓ) Inv
      (modify fun sC : LibsignalToModularSchemeSimState PQ Pt ℓ => { sC with kept := f sC.kept }) := by
  intro sC gh hpq r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1a_pres_pq_modify_amb (Inv : PQ → Prop) :
    c1a_pres_pq (Pt := Pt) (ℓ := ℓ) Inv
      (modify fun sC : LibsignalToModularSchemeSimState PQ Pt ℓ =>
        { sC with base := { sC.base with amb := sC.base.amb + 1 } }) := by
  intro sC gh hpq r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1a_pres_pq_zoomB_fwd (Inv : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1a_pres_pq Inv (runOnBaseState (probeHook fig qepF) (LibsignalSim.fwd Q c')) := by
  intro sC gh hpq r hr
  rw [c1a_zoomB_probeHook_run] at hr
  simp only [LibsignalSim.fwd, LibsignalSim.liftQ, StateT.run_bind, StateT.run_get,
    pure_bind] at hr
  split at hr <;>
  · simp only [StateT.run_lift, map_eq_bind_pure_comp, simulateQ_bind, Function.comp_apply,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact hpq

private theorem c1a_pres_pq_zoomB_onAccept (Inv : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (hpq' : Inv pq') :
    c1a_pres_pq Inv
      (runOnBaseState (probeHook fig qepF) (LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq')) := by
  intro sC gh hpq r hr
  rw [c1a_zoomB_probeHook_run, onAccept_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact c1a_onAcceptPure_pqInv Inv qep Q w isDel t i m ci? T pq' sC.base hpq hpq'

private theorem c1a_pres_pq_zoomB_onAnswer (Inv : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (hpq' : Inv pq') :
    c1a_pres_pq Inv
      (runOnBaseState (probeHook fig qepF) (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res)) := by
  intro sC gh hpq r hr
  rw [c1a_zoomB_probeHook_run, onAnswer_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact c1a_onAnswerPure_pqInv Inv qep Q w isDel ci? T pq' res sC.base hpq hpq'

private theorem c1a_pres_pq_fwdAnswerC (Inv : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hpq' : Inv pq') :
    c1a_pres_pq Inv (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine c1a_pres_pq_bind (c1a_pres_pq_zoomB_fwd Inv fig qepF Q c') fun res => ?_
  cases res with
  | none => exact c1a_pres_pq_zoomB_onAnswer Inv qep fig qepF Q w isDel ci? T pq' none hpq'
  | some r =>
    cases r with
    | accepted t i pm =>
      exact c1a_pres_pq_bind
        (c1a_pres_pq_modify_kept Inv (fun kept => Function.update kept Q (Kept.recv fig fs c' (kept Q))))
        fun _ => c1a_pres_pq_zoomB_onAnswer Inv qep fig qepF Q w isDel ci? T pq' _ hpq'
    | rejected =>
      exact c1a_pres_pq_zoomB_onAnswer Inv qep fig qepF Q w isDel ci? T pq' _ hpq'

private theorem c1a_pres_pq_resyncC (Inv : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) (hpq' : Inv pq') :
    c1a_pres_pq Inv (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact c1a_pres_pq_pure Inv _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine c1a_pres_pq_bind (c1a_pres_pq_liftC Inv fig qepF _) fun res => ?_
    cases res with
    | none => exact c1a_pres_pq_pure Inv _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact c1a_pres_pq_bind
          (c1a_pres_pq_modify_kept Inv (fun kept => Function.update kept Q (Kept.recv fig fs c (kept Q))))
          fun _ => c1a_pres_pq_zoomB_onAccept Inv qep fig qepF Q w true t i pm.2 ci? T pq' hpq'
      | _ => exact c1a_pres_pq_pure Inv _

private theorem c1a_pres_pq_fwdC (P : Params PQ PQC) (Inv : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) (hpq' : Inv pq') :
    c1a_pres_pq Inv (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine c1a_pres_pq_bind (c1a_pres_pq_get Inv) fun sC => ?_
  cases honestC with
  | none => exact c1a_pres_pq_fwdAnswerC Inv qep fig fs qepF Q w isDel ci? T pq' c' hpq'
  | some c =>
    refine c1a_pres_pq_ite ?_ (c1a_pres_pq_fwdAnswerC Inv qep fig fs qepF Q w isDel ci? T pq' c' hpq')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact c1a_pres_pq_resyncC Inv qep fig fs qepF Q w ci? T pq' c r hpq'
    | none =>
      exact c1a_pres_pq_bind (c1a_pres_pq_probe Inv fig qepF Q c') fun _ =>
        c1a_pres_pq_pure Inv _

private theorem c1a_pres_pq_fwdEvictC (Inv : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hpq' : Inv pq') :
    c1a_pres_pq Inv (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine c1a_pres_pq_bind (c1a_pres_pq_get Inv) fun sC => ?_
  refine c1a_pres_pq_ite ?_ (c1a_pres_pq_fwdAnswerC Inv qep fig fs qepF Q w isDel none T pq' c' hpq')
  exact c1a_pres_pq_bind (c1a_pres_pq_probe Inv fig qepF Q c') fun _ => c1a_pres_pq_pure Inv _

private theorem c1a_pres_pq_guardC {α : Type} {Inv : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : c1a_pres_pq Inv m) :
    c1a_pres_pq Inv (guardC m) := by
  unfold guardC
  refine c1a_pres_pq_bind (c1a_pres_pq_get Inv) fun sC => ?_
  exact c1a_pres_pq_ite (c1a_pres_pq_pure Inv none) hm

private theorem c1a_pres_pq_simRecvC (P : Params PQ PQC) (Inv : PQ → Prop)
    (hrecv : ∀ st msg st' salt, Inv st → P.spqr.recv st msg = .ok (st', salt) → Inv st')
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    c1a_pres_pq Inv (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  intro sC gh hpq r hr
  unfold simRecvC at hr
  generalize (2 ^ 32 : ℕ) = maxI at hr
  generalize (25000 : ℕ) = maxSkip at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  have hm : c1a_pres_pq Inv (do
      let s := sC.base
      if s.mir.win then return none
      if isDel && (s.mir.inTransit Q.other w).isNone then return none
      if !isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
          || !(ratchetKeyAdmissible P.codec decT encT w)) then return none
      if w.length < 9 then return some .rejected
      let ser := w.take (w.length - 8)
      let tag := bytesToWord64LE (w.drop (w.length - 8))
      match (signalWireCodec P.codec).parse ser with
      | none => return some .rejected
      | some (h, _) =>
        if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then return some .rejected
        if P.spqr.recvPanics (s.pq Q) h.pqRatchet then return some .rejected
        match P.spqr.recv (s.pq Q) h.pqRatchet with
        | .error _ => return some .rejected
        | .ok (pq', salt) =>
          let i := h.counter.toNat + 1
          let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
          let mkC (t : ℕ) (T : Option Pt) : Fig8C Pt :=
            match honestC with
            | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
            | none => ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
          let T? := decT h.senderRatchetKey
          let spkAmb := Q == Party.A && (s.chains Q).any (·.key.isNone)
          match (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
          | some ci =>
            let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
            if g.rejects i then return some .rejected
            fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := probeHook fig qepF)
              Q w isDel (some ci) h.senderRatchetKey pq' honestC (mkC g.epoch T?)
          | none =>
            let evicted := (honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true
            if evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true then
              return some .rejected
            if T? == some 0 then return some .rejected
            if inReceiveOnlyEpoch s.mir Q || spkAmb then
              modify fun sC => { sC with base := { sC.base with amb := sC.base.amb + 1 } }
            if inReceiveOnlyEpoch s.mir Q || maxSkip < i - 1 || maxI ≤ i then return some .rejected
            match T? with
            | none => return some .rejected
            | some T =>
              if evicted then
                fwdEvictC (qep := qep) (fig := fig) (fs := fs) (H := probeHook fig qepF) Q w isDel
                  h.senderRatchetKey pq' ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
              else
                fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := probeHook fig qepF)
                  Q w isDel none h.senderRatchetKey pq' honestC
                  (mkC (s.mir.epoch Q + 1) (some T))) := by
    dsimp only
    refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
    refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
    refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
    refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
    cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
    | none => exact c1a_pres_pq_pure Inv _
    | some hb =>
      rcases hb with ⟨h, _⟩
      dsimp only
      refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
      refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
      cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
      | error _ => exact c1a_pres_pq_pure Inv _
      | ok ps =>
        rcases ps with ⟨pq', salt⟩
        have hpq' : Inv pq' := hrecv (sC.base.pq Q) h.pqRatchet pq' salt (hpq Q) hspqr
        dsimp only
        cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
        | some ci =>
          dsimp only
          refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
          exact c1a_pres_pq_fwdC P Inv qep fig fs qepF Q w isDel
            (some ci) h.senderRatchetKey pq' _ _ hpq'
        | none =>
          dsimp only
          refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
          refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
          refine c1a_pres_pq_ite
            (c1a_pres_pq_bind (c1a_pres_pq_modify_amb Inv) fun _ => ?_) ?_ <;>
          · refine c1a_pres_pq_ite (c1a_pres_pq_pure Inv _) ?_
            cases decT h.senderRatchetKey with
            | none => exact c1a_pres_pq_pure Inv _
            | some T =>
              exact c1a_pres_pq_ite
                (c1a_pres_pq_fwdEvictC Inv qep fig fs qepF Q w isDel h.senderRatchetKey pq' _ hpq')
                (c1a_pres_pq_fwdC P Inv qep fig fs qepF Q w isDel
                  none h.senderRatchetKey pq' _ _ hpq')
  exact hm sC gh hpq r hr

private theorem c1a_pres_pq_simCorrC (P : Params PQ PQC) (Inv : PQ → Prop) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    c1a_pres_pq Inv (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  intro sC gh hpq r hr
  unfold simCorrC at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hcond : sC.base.mir.win || !(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q ||
      !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)
  · simp [hcond] at hr
    subst hr
    exact hpq
  · simp only [hcond, Bool.false_eq_true, ite_false] at hr
    have hm : c1a_pres_pq Inv (do
        let res ← LibsignalSimC.liftC (probeHook fig qepF)
          (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)
        match res with
        | none => return none
        | some st =>
          let chains := if Q == Party.B && sC.base.mir.epoch Party.B == 0 then
              match st.γ with
              | .exp x => Function.update sC.base.chains Party.A ((sC.base.chains Party.A).map fun g =>
                  if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
              | _ => sC.base.chains
            else sC.base.chains
          let g := LibsignalSim.toGhost (P := P) { sC.base with chains } Q st
          set { sC with base := { sC.base with mir := sC.base.mir.afterCorr Q, chains },
                        kept := Function.update sC.kept Q (Kept.ofSt st),
                        snaps := (Q, sC.base.mir.epoch Q, g) :: sC.snaps }
          return some g) := by
      refine c1a_pres_pq_bind (c1a_pres_pq_liftC Inv fig qepF _) fun res => ?_
      cases res with
      | none => exact c1a_pres_pq_pure Inv _
      | some st =>
        intro sC₁ gh₁ _ r₁ hr₁
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr₁
        subst hr₁
        exact hpq
    exact hm sC gh hpq r hr

private theorem c1a_mkPub_invB (P : Params PQ PQC) {q r : ℕ} {Inv : ℕ → PQ → Prop}
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32)
    (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hpq : ∀ R, InvB Inv q r (s.pq R))
    (hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub)) :
    InvB Inv q (r - 1) pq' := by
  unfold LibsignalSim.mkPub at hmk
  rw [Option.map_eq_some_iff] at hmk
  rcases hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  have hpq' : st' = pq' := congrArg Prod.fst hpair
  subst hpq'
  exact InvB.send hS hr0 (hpq Q) hsend

private theorem c1a_stepSim_send_pqInvB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rc : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, InvB Inv q r (st.1.pq R))
    (z : Option (List (BitVec 8)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hz : z ∈ support (
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
        SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
      (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal rc)).run st.1)).run st.2 >>=
        (fun x => pure (x.1.1, (x.1.2, x.2))))) :
    ∀ R, InvB Inv q (r - 1) (z.2.1.pq R) := by
  have hpqm : ∀ R, InvB Inv q (r - 1) (st.1.pq R) :=
    fun R => InvB.mono (by omega) (hpq R)
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  change z ∈ support ((simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal rc)).run st.1)).run st.2 >>=
    (fun x => pure (x.1.1, (x.1.2, x.2)))) at hz
  unfold LibsignalSim.guard LibsignalSim.simSend at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hstop : st.1.stopped
  · simp [hstop] at hz; subst hz; exact hpqm
  · simp only [hstop, Bool.false_eq_true, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir] at hz; subst hz; exact hpqm
    · simp only [hmir, Bool.false_eq_true, ite_false] at hz
      cases hep : st.1.mir.epMgmt 3 qep Q rc.isSome with
      | none => simp [hep] at hz; subst hz; exact hpqm
      | some s₁ =>
        simp only [hep] at hz
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch] at hz; subst hz; exact hpqm
        · simp only [hch, Bool.false_eq_true, ite_false] at hz
          cases rc with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨c_cka, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpqm
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : InvB Inv q (r - 1) pq' :=
                c1a_mkPub_invB P hS hr0 st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, InvB Inv q (r - 1) (Function.update st.1.pq Q pq' R) :=
                c1a_pq_update_inv hpqm hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpqm
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpqm
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpqm
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpqm
                  · exact hupd
          | none =>
            simp only [pure_bind, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rq, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpqm
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : InvB Inv q (r - 1) pq' :=
                c1a_mkPub_invB P hS hr0 st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, InvB Inv q (r - 1) (Function.update st.1.pq Q pq' R) :=
                c1a_pq_update_inv hpqm hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpqm
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpqm
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpqm
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpqm
                  · exact hupd

private theorem c1a_stepSimCNone_pqInvB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ)
    (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x),
      ∀ R, InvB Inv q (r - 1) (z.2.1.base.pq R) := by
  have hpqm : ∀ R, InvB Inv q (r - 1) (x.1.base.pq R) :=
    fun R => InvB.mono (by omega) (hpq R)
  intro z hz
  rcases q_sm with ((((⟨Q, m₀, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rw [c1a_stepSimCNone_transmit_eq, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rw [c1a_cxSend_base]
    exact c1a_stepSim_send_pqInvB P Inv ℓ Dh encPt encT idOf lam qep q r hS hr0 Q m₀ none rc
      x.sim hpq res (by simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres)
  · rw [c1a_stepSimCNone_chall_eq, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rw [c1a_cxSend_base]
    exact c1a_stepSim_send_pqInvB P Inv ℓ Dh encPt encT idOf lam qep q r hS hr0 Q m₀ (some m₁) rc
      x.sim hpq res (by simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres)
  · unfold stepSimCNone at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨r₁, hr₁, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact c1a_pres_pq_guardC
      (c1a_pres_pq_simRecvC P (InvB Inv q (r - 1)) (spqrCLocal_closedRecv hS) encT decT qep _ _
        (qep + 1) Q w true) x.1 x.2 hpqm r₁ hr₁
  · unfold stepSimCNone at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨r₁, hr₁, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact c1a_pres_pq_guardC
      (c1a_pres_pq_simRecvC P (InvB Inv q (r - 1)) (spqrCLocal_closedRecv hS) encT decT qep _ _
        (qep + 1) Q w false) x.1 x.2 hpqm r₁ hr₁
  · unfold stepSimCNone at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨r₁, hr₁, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact c1a_pres_pq_guardC
      (c1a_pres_pq_simCorrC P (InvB Inv q (r - 1)) encT _ (qep + 1) Dh Q) x.1 x.2 hpqm r₁ hr₁

private theorem c1a_evalDist_bind_congr_support {α : Type}
    (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact evalDist_bind_congr _ _ _ fun u =>
      ih u fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

private theorem c1a_evalDist_runSimCEager_none {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (hS : SpqrCLocal P.spqr q Inv)
    (x : JointC PQ Pt ℓ)
    (F : α → JointC PQ Pt ℓ → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q)) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa x ec >>= fun res =>
        F res.1 res.2.1 res.2.2)] =
      𝒟[c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep oa x >>= fun res =>
        withEagerCoins res.2.1.base.mir (F res.1 res.2)] := by
  induction oa using OracleComp.inductionOn generalizing r x with
  | pure a =>
    simp only [runSimCEager_pure, c1a_runSimCNone_pure, pure_bind]
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    cases t with
    | inl u =>
      have hq' : ∀ y, (cont y).IsQueryBoundP p r := fun y => by simpa [hp_inl u] using hq.2 y
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inl_bind, c1a_runSimCNone_inl_bind, bind_assoc]
      rw [evalDist_withEagerCoins_bind_swap x.1.base.mir
        (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _)]
      refine evalDist_bind_congr _ _ _ fun y => ?_
      exact ih y r (hq' y) x hpq
    | inr q_sm =>
      have hr0 : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by
        simpa [hp_inr q_sm] using hq.2 ans
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inr_bind, c1a_runSimCNone_inr_bind, bind_assoc]
      rw [c1a_evalDist_stepSimCEager_none P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep q_sm x
        (fun ans x' ec' =>
          runSimCEager P ℓ Dh encPt encT decT idOf lam qep none (cont ans) x' ec' >>= fun res =>
          F res.1 res.2.1 res.2.2) hpq (spqrCLocal_total hS hr0)]
      refine c1a_evalDist_bind_congr_support _ _ _ fun res hres => ?_
      exact ih res.1 (r - 1) (hq' res.1) res.2
        (c1a_stepSimCNone_pqInvB P Inv ℓ Dh encPt encT decT idOf lam qep q r hS hr0 q_sm x hpq res hres)

private theorem c1a_evalDist_runSimCNone_eq_withEagerCoins_runSimCEager
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) (hS : SpqrCLocal P.spqr q Inv)
    (x : JointC PQ Pt ℓ)
    (G : Bool → JointC PQ Pt ℓ → ProbComp Bool)
    (hpq : ∀ Q, InvB Inv q q (x.1.base.pq Q)) :
    𝒟[c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A x >>= fun r => G r.1 r.2] =
      𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep none A x ec >>= fun r =>
        G r.1 r.2.1)] := by
  rw [c1a_evalDist_runSimCEager_none P Inv ℓ Dh encPt encT decT idOf lam qep q q
    (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq hS x (fun a s _ => G a s) hpq]
  refine evalDist_bind_congr _ _ _ fun r => ?_
  exact (evalDist_withEagerCoins_const r.2.1.base.mir (G r.1 r.2)).symm

private theorem c1a_initSimC_pqInvB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (q : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (pqrKey : BitVec 256) :
    ∀ Q, InvB Inv q q
      ((initSimC (Pt := Pt) (ℓ := ℓ) (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).base.pq Q) := by
  intro Q
  cases Q <;> simpa [initSimC, initSim] using InvB.init hS _ pqrKey

/-- Equates the H1 game distribution with `libsignalToModularSchemeSim` to the eager C run from the
initial joint state. -/
theorem evalDist_game_simRunC_none_eq_eagerC (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : ℕ) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[SM.game sm (2 + 1) (qep + 1) SM.Config.h1 (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runSimCEager P ℓ Dh encPt encT decT idOf lam qep none A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>= fun z =>
            pure (b == z.1 || z.2.1.2.1.win)] := by
  intro sm
  rw [c1a_game_simRunC_none_eq_runSimCNone]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false) >>= fun z =>
          pure (b == z.1 || z.2.2.1.win)] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runSimCEager P ℓ Dh encPt encT decT idOf lam qep none A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>= fun z =>
            pure (b == z.1 || z.2.1.2.1.win)] := by
    intro pqrKey
    rw [c1a_evalDist_runSimCNone_eq_withEagerCoins_runSimCEager P Inv ℓ Dh encPt encT decT idOf lam
      qep q A hq hS
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
       SM.initState sm (k_root, x₀) b, false)
      (fun a s => pure (b == a || s.2.1.win))
      (c1a_initSimC_pqInvB P Inv q hS pqrKey)]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

private def c1b_rel {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    (m_id : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (m_pr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (simulateQ (fig8ImplH1 fig qepF) (m_id.run sC)).run gh.1 =
      ((m_pr.run sC).run gh >>= fun r => pure (r.1, r.2.1))

private theorem c1b_rel_pure {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (a : α) :
    c1b_rel (PQ := PQ) fig qepF (pure a) (pure a) := by
  intro sC gh
  simp [StateT.run_pure]

private theorem c1b_rel_bind {α β : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    {m_id : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {m_pr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k_id : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β}
    {k_pr : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : c1b_rel fig qepF m_id m_pr)
    (hk : ∀ a, c1b_rel fig qepF (k_id a) (k_pr a)) :
    c1b_rel fig qepF (m_id >>= k_id) (m_pr >>= k_pr) := by
  intro sC gh
  simp only [StateT.run_bind, simulateQ_bind, hm sC gh, bind_assoc, pure_bind]
  congr 1
  funext r
  exact hk r.1.1 r.1.2 r.2

private theorem c1b_rel_get
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) :
    c1b_rel (PQ := PQ) fig qepF get get := by
  intro sC gh
  simp [StateT.run_get]

private theorem c1b_rel_set
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    c1b_rel (PQ := PQ) fig qepF (set sC') (set sC') := by
  intro sC gh
  simp [StateT.run_set]

private theorem c1b_rel_modify
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    c1b_rel (PQ := PQ) fig qepF (modify f) (modify f) := by
  intro sC gh
  simp [StateT.run_modify]

private theorem c1b_rel_ite {α : Type} {P_cond : Prop} [Decidable P_cond]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    {t_id e_id : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {t_pr e_pr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : c1b_rel fig qepF t_id t_pr) (he : c1b_rel fig qepF e_id e_pr) :
    c1b_rel fig qepF (if P_cond then t_id else e_id) (if P_cond then t_pr else e_pr) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem c1b_probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (y : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift y).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) y).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

private theorem c1b_probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem c1b_rel_zoomB {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    c1b_rel (PQ := PQ) fig qepF (runOnBaseState idHook x) (runOnBaseState (probeHook fig qepF) x) := by
  intro sC gh
  change (simulateQ (fig8ImplH1 fig qepF)
      (x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 }))).run gh.1 =
    ((((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
      pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh >>= fun r => pure (r.1, r.2.1))
  rw [StateT.run_bind, c1b_probeHook_lift_run]
  simp [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]

private theorem c1b_rel_liftC {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    c1b_rel (PQ := PQ) fig qepF
      (LibsignalSimC.liftC idHook x) (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh
  change (simulateQ (fig8ImplH1 fig qepF)
      (x >>= fun a => pure (a, sC))).run gh.1 =
    ((((probeHook fig qepF).lift x >>= fun a =>
      pure (a, sC)) : ProbeM Pt ℓ _).run gh >>= fun r => pure (r.1, r.2.1))
  rw [StateT.run_bind, c1b_probeHook_lift_run]
  simp [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]

private theorem c1b_rel_probe
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1b_rel (PQ := PQ) fig qepF
      (StateT.lift ((idHook (ℓ := ℓ)).probe Q c'))
      (StateT.lift ((probeHook fig qepF).probe Q c')) := by
  intro sC gh
  change (simulateQ (fig8ImplH1 fig qepF) (pure ((), sC))).run gh.1 =
    ((((probeHook fig qepF).probe Q c' >>= fun a =>
      pure (a, sC)) : ProbeM Pt ℓ _).run gh >>= fun r => pure (r.1, r.2.1))
  rw [StateT.run_bind, c1b_probeHook_probe_run]
  simp

private theorem c1b_rel_guardC {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    {m_id : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)}
    {m_pr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : c1b_rel fig qepF m_id m_pr) :
    c1b_rel fig qepF (guardC m_id) (guardC m_pr) := by
  unfold guardC
  refine c1b_rel_bind fig qepF (c1b_rel_get fig qepF) fun sC => ?_
  exact c1b_rel_ite fig qepF (c1b_rel_pure fig qepF none) hm

private theorem c1b_rel_simSendC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    c1b_rel fig qepF
      (simSendC P qep fig idHook Q m₀ chal r)
      (simSendC P qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendC
  refine c1b_rel_bind fig qepF (c1b_rel_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact c1b_rel_pure fig qepF none
  | some w =>
    refine c1b_rel_bind fig qepF (c1b_rel_get fig qepF) fun sC => ?_
    exact c1b_rel_bind fig qepF (c1b_rel_set fig qepF _) fun _ => c1b_rel_pure fig qepF (some w)

private theorem c1b_rel_fwdAnswerC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    c1b_rel fig qepF
      (fwdAnswerC qep fig fs idHook Q w isDel ci? T pq' c')
      (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine c1b_rel_bind fig qepF (c1b_rel_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact c1b_rel_zoomB (PQ := PQ) fig qepF _
  | some r =>
    cases r <;>
      first
      | exact c1b_rel_zoomB (PQ := PQ) fig qepF _
      | exact c1b_rel_bind fig qepF (c1b_rel_modify fig qepF _) fun _ =>
          c1b_rel_zoomB (PQ := PQ) fig qepF _

private theorem c1b_rel_resyncC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    c1b_rel fig qepF
      (resyncC qep fig fs idHook Q w ci? T pq' c r)
      (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact c1b_rel_pure fig qepF _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine c1b_rel_bind fig qepF (c1b_rel_liftC fig qepF _) fun res => ?_
    cases res with
    | none => exact c1b_rel_pure fig qepF _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact c1b_rel_bind fig qepF (c1b_rel_modify fig qepF _) fun _ =>
          c1b_rel_zoomB (PQ := PQ) fig qepF _
      | _ => exact c1b_rel_pure fig qepF _

private theorem c1b_rel_fwdC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    c1b_rel fig qepF
      (fwdC P qep fig fs idHook Q w isDel ci? T pq' honestC c')
      (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine c1b_rel_bind fig qepF (c1b_rel_get fig qepF) fun sC => ?_
  cases honestC with
  | none => exact c1b_rel_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    refine c1b_rel_ite fig qepF ?_ (c1b_rel_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact c1b_rel_resyncC qep fig fs qepF Q w ci? T pq' c r
    | none =>
      exact c1b_rel_bind fig qepF (c1b_rel_probe fig qepF Q c') fun _ =>
        c1b_rel_pure fig qepF _

private theorem c1b_rel_fwdEvictC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    c1b_rel fig qepF
      (fwdEvictC qep fig fs idHook Q w isDel T pq' c')
      (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine c1b_rel_bind fig qepF (c1b_rel_get fig qepF) fun sC => ?_
  refine c1b_rel_ite fig qepF ?_ (c1b_rel_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c')
  exact c1b_rel_bind fig qepF (c1b_rel_probe fig qepF Q c') fun _ => c1b_rel_pure fig qepF _

private theorem c1b_rel_simRecvC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    c1b_rel fig qepF
      (simRecvC P encT decT qep fig fs idHook Q w isDel)
      (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine c1b_rel_bind fig qepF (c1b_rel_get fig qepF) fun sC => ?_
  dsimp only
  refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
  refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
  refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
  refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact c1b_rel_pure fig qepF _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
    refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact c1b_rel_pure fig qepF _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
        exact c1b_rel_fwdC P qep fig fs qepF Q w isDel (some ci) h.senderRatchetKey pq' _ _
      | none =>
        dsimp only
        refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
        refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
        refine c1b_rel_ite fig qepF
          (c1b_rel_bind fig qepF (c1b_rel_modify fig qepF _) fun _ => ?_) ?_ <;>
        · refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
          cases decT h.senderRatchetKey with
          | none => exact c1b_rel_pure fig qepF _
          | some T =>
            exact c1b_rel_ite fig qepF
              (c1b_rel_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (c1b_rel_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)

private theorem c1b_rel_simCorrC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    c1b_rel fig qepF
      (simCorrC P encT idHook Dh Q)
      (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine c1b_rel_bind fig qepF (c1b_rel_get fig qepF) fun sC => ?_
  refine c1b_rel_ite fig qepF (c1b_rel_pure fig qepF _) ?_
  refine c1b_rel_bind fig qepF (c1b_rel_liftC fig qepF _) fun res => ?_
  cases res with
  | none => exact c1b_rel_pure fig qepF _
  | some st =>
    exact c1b_rel_bind fig qepF (c1b_rel_set fig qepF _) fun _ => c1b_rel_pure fig qepF _

private theorem c1b_rel_simImplC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    c1b_rel fig qepF
      (simImplC P encT decT qep fig fs idHook Dh t)
      (simImplC P encT decT qep fig fs (probeHook fig qepF) Dh t) := by
  rcases t with u | (((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · exact c1b_rel_liftC fig qepF _
  · exact c1b_rel_guardC fig qepF (c1b_rel_simSendC P qep fig qepF Q m₀ none r')
  · exact c1b_rel_guardC fig qepF (c1b_rel_simSendC P qep fig qepF Q m₀ (some m₁) r')
  · exact c1b_rel_guardC fig qepF (c1b_rel_simRecvC P encT decT qep fig fs qepF Q w true)
  · exact c1b_rel_guardC fig qepF (c1b_rel_simRecvC P encT decT qep fig fs qepF Q w false)
  · exact c1b_rel_guardC fig qepF (c1b_rel_simCorrC P encT fig qepF Dh Q)

private theorem c1b_rel_simulateQ {α : Type} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α) :
    c1b_rel fig qepF
      (simulateQ (simImplC P encT decT qep fig fs idHook Dh) oa)
      (simulateQ (simImplC P encT decT qep fig fs (probeHook fig qepF) Dh) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [simulateQ_pure]
    exact c1b_rel_pure fig qepF a
  | query_bind t cont ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    exact c1b_rel_bind fig qepF (c1b_rel_simImplC P encT decT qep fig fs qepF Dh t) ih

private def c1b_runSimCNone {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) :
    ProbComp (α × JointC PQ Pt ℓ) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  (((simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := probeHook fig (qep + 1)) Dh) oa).run
      x.1).run x.2) >>= fun r => pure (r.1.1, (r.1.2, r.2))

private theorem c1b_runSimCNone_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (a : α) (x : JointC PQ Pt ℓ) :
    c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep (pure a) x = pure (a, x) := by
  simp [c1b_runSimCNone]

private theorem c1b_runSimCNone_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) :
    c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont) x =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep (cont y) x := by
  dsimp only [c1b_runSimCNone]
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have h1 :
      StateT.run (StateT.run (liftM (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := probeHook fig (qep + 1)) Dh (.inl u)) :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) _) x.1) x.2 =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        pure ((y, x.1), x.2)) := by
    change ((((probeHook fig (qep + 1)).lift
      (OracleSpec.query (spec := unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl u)) >>=
      fun y => pure (y, x.1)) : ProbeM Pt ℓ _).run x.2) = _
    rw [StateT.run_bind, c1b_probeHook_lift_run]
    simp only [bind_assoc, pure_bind, StateT.run_pure, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_eq, id_map]
    have h2 :
        (fig8ImplH1 fig (qep + 1) (.inl u)).run x.2.1 =
        ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y => pure (y, x.2.1)) := rfl
    rw [h2]
    simp [bind_assoc, pure_bind]
  dsimp only [fig] at h1
  rw [h1]
  simp [bind_assoc, pure_bind]

private theorem c1b_runSimCNone_inr_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) :
    c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont) x =
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x >>= fun r =>
        c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep (cont r.1) r.2 := by
  dsimp only [c1b_runSimCNone, stepSimCNone]
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind,
    bind_assoc, pure_bind]
  rfl

private theorem c1b_simCNoneWinEvent_eq_runSimCNone (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k_fig8 =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
              (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k_fig8 b, false) >>= fun z =>
              pure z.2.2.1.win) := by
  intro sm
  have hid : ∀ {α : Type} (m : Fig8Comp Pt ℓ α),
      (idHook (Pt := Pt) (ℓ := ℓ)).lift m = m := fun _ => rfl
  unfold simCNoneWinEvent SM.run Refine.libsignalToModularSchemeSim runLibsignalToModularSchemeSim simRunCWith
  dsimp only
  simp only [bind_assoc]
  congr 1; funext b
  congr 1; funext k_fig8
  simp only [hid, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [Construction.AuthL11.simulateQ_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  congr 1; funext pqrKey
  have hrel := c1b_rel_simulateQ P encT decT qep sm (lFS P.C P.codec ℓ encT idOf 25000) (qep + 1) Dh A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (SM.initState sm k_fig8 b, false)
  unfold fig8ImplH1 at hrel
  dsimp only [sm] at hrel ⊢
  rw [hrel]
  simp [c1b_runSimCNone, bind_assoc, pure_bind, sm]

private theorem c1b_cxSend_base (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (x : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q x s' res).base = s' := by
  cases res <;> rfl

private theorem c1b_zoomB_probeHook_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (m : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    (((runOnBaseState (probeHook fig qepF) m).run sC).run gh) =
      ((simulateQ (fig8ImplH1 fig qepF) (m.run sC.base)).run gh.1 >>= fun r =>
        pure ((r.1.1, { sC with base := r.1.2 }), (r.2, gh.2))) := by
  change ((do
    let __x ← (probeHook fig qepF).lift (m.run sC.base)
    pure (__x.1, { sC with base := __x.2 })).run gh) = _
  rw [StateT.run_bind, c1b_probeHook_lift_run]
  simp [bind_assoc, pure_bind]

private theorem c1b_stepSimCNone_send_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (x : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (((guardC (simSendC P qep fig (probeHook fig (qep + 1)) Q m₀ chal r)).run x.1).run x.2 >>=
      fun res => pure (res.1.1, (res.1.2, res.2))) =
    ((simulateQ (fig8ImplH1 fig (qep + 1))
        ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run x.1.base)).run x.2.1 >>=
      fun res => pure (res.1.1, (cxSend P Dh encPt encT idOf lam Q x.1 res.1.2 res.1.1, res.2, x.2.2))) := by
  intro fig
  unfold guardC simSendC LibsignalSim.guard
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : x.1.base.stopped
  · simp [hstop, cxSend]
  · simp only [hstop, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, c1b_zoomB_probeHook_run,
      bind_assoc, pure_bind]
    congr 1; funext res
    rcases res with ⟨⟨ans, s'⟩, g'⟩
    cases ans with
    | none => simp [cxSend]
    | some w =>
      simp only [cxSend, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        pure_bind, fig]
      rfl

private theorem c1b_stepSimCNone_transmit_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC) (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inl (Q, m₀, r))))) x =
      (stepSim P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inl (.inl (Q, m₀, r))))) x.sim >>=
        fun res => pure (res.1, (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2))) := by
  have h := c1b_stepSimCNone_send_eq P ℓ Dh encPt encT idOf lam qep Q m₀ none r x
  simpa [stepSimCNone, simImplC, stepSim, stepSimNone, LibsignalSim.simImpl, fig8ImplH1,
    JointC.sim, bind_assoc, pure_bind] using h

private theorem c1b_stepSimCNone_chall_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC) (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) x =
      (stepSim P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) x.sim >>=
        fun res => pure (res.1, (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2))) := by
  have h := c1b_stepSimCNone_send_eq P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r x
  simpa [stepSimCNone, simImplC, stepSim, stepSimNone, LibsignalSim.simImpl, fig8ImplH1,
    JointC.sim, bind_assoc, pure_bind] using h

private theorem c1b_simRecvUsesCoin_none (P : Params PQ PQC)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvUsesCoin P encT decT none Q w isDel st = false := by
  have hne : ((none : Option ℕ) == some st.1.amb) = false := rfl
  unfold simRecvUsesCoin
  dsimp only
  simp only [hne, Bool.and_false, ↓reduceIte]
  repeat' (first | split | rfl | contradiction)

private theorem c1b_simRecvStep_none_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st).2.1.stopped =
      st.1.stopped := by
  rcases st with ⟨⟨mir, pq, pn, unackA, honest, chains, amb, stopped⟩, s_fig8⟩
  have hne : ((none : Option ℕ) == some amb) = false := rfl
  unfold simRecvStep
  dsimp only
  cases stopped
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hmir : mir.win
    · simp only [hmir, ite_true]
    · simp only [hmir, Bool.false_eq_true, ite_false]
      by_cases hdel : isDel && (mir.inTransit Q.other w).isNone
      · simp only [hdel, ite_true]
      · simp only [hdel, Bool.false_eq_true, ite_false]
        by_cases hinj : !isDel && ((mir.inTransit Q.other w).isSome || !(mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))
        · simp only [hinj, ite_true]
        · simp only [hinj, Bool.false_eq_true, ite_false]
          by_cases hlen : w.length < 9
          · simp only [hlen, ite_true]
          · simp only [hlen, ite_false]
            cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
            | none => rfl
            | some hp =>
              rcases hp with ⟨h, _⟩
              dsimp only
              by_cases haddr : !(addressCheckPasses h.addresses (P.expectedAddrs Q))
              · simp only [haddr, ite_true]
              · simp only [haddr, Bool.false_eq_true, ite_false]
                cases P.spqr.recv (pq Q) h.pqRatchet with
                | error _ => rfl
                | ok ps =>
                  rcases ps with ⟨pq', salt⟩
                  dsimp only
                  cases (chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
                  | some ci =>
                    dsimp only
                    by_cases hrej : ((chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1)
                    · simp only [hrej, ite_true]
                    · simp only [hrej, Bool.false_eq_true, ite_false, onAnswerPure_stopped]
                  | none =>
                    dsimp only
                    simp only [hne, Bool.and_false, Bool.false_eq_true, ite_false]
                    by_cases hev : (((honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map fun c => decide (c.1.1 ≠ mir.epoch Q + 1)) == some true
                    · simp only [hev, ite_true]
                    · simp only [hev, Bool.false_eq_true, ite_false]
                      by_cases hzero : decT h.senderRatchetKey == some 0
                      · simp only [hzero, ite_true]
                      · simp only [hzero, Bool.false_eq_true, ite_false]
                        by_cases hamb : inReceiveOnlyEpoch mir Q || (Q == Party.A && (chains Q).any (·.key.isNone)) <;>
                        · simp only [hamb, ite_true, Bool.false_eq_true, ite_false]
                          by_cases hcond : inReceiveOnlyEpoch mir Q || 25000 < h.counter.toNat + 1 - 1 || 2 ^ 32 ≤ h.counter.toNat + 1
                          · simp only [hcond, ite_true]
                          · simp only [hcond, Bool.false_eq_true, ite_false]
                            cases decT h.senderRatchetKey <;> simp only [onAnswerPure_stopped]
  · simp only [ite_true]

private theorem c1b_simRecvStops_none (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w isDel st = false := by
  unfold simRecvStops
  rw [c1b_simRecvStep_none_stopped]
  cases st.1.stopped <;> simp

private theorem c1b_stepSimC_none (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) :
    stepSimC P ℓ Dh encPt encT decT idOf lam qep none q_sm x =
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSimC, c1b_simRecvStops_none]

private theorem c1b_evalDist_stepSimCEager (P : Params PQ PQC) (Inv' : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ)
    (G : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      JointC PQ Pt ℓ → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv' (x.1.base.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv') :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm x ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x >>= fun r =>
        withEagerCoins r.2.1.base.mir (G r.1 r.2)] := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · dsimp only [stepSimCEager, stepSimCEagerTransmit]
    simp only [bind_assoc, pure_bind]
    have h := evalDist_stepSimEagerTransmitW P Inv' ℓ Dh encPt encT decT idOf lam qep none Q m₀ r x.sim
      (fun ans st' ec' => G ans (cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2) ec')
      hpq hW0
    simpa only [JointC.sim, c1b_stepSimCNone_transmit_eq, bind_assoc, pure_bind,
      c1b_cxSend_base] using h
  · dsimp only [stepSimCEager, stepSimCEagerChall]
    simp only [bind_assoc, pure_bind]
    have h := evalDist_stepSimEagerChallW P Inv' ℓ Dh encPt encT decT idOf lam qep none Q m₀ m₁ r x.sim
      (fun ans st' ec' => G ans (cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2) ec')
      hpq hW0
    simpa only [JointC.sim, c1b_stepSimCNone_chall_eq, bind_assoc, pure_bind,
      c1b_cxSend_base] using h
  · dsimp only [stepSimCEager, stepSimCEagerDeliver]
    rw [c1b_simRecvUsesCoin_none, evictStopsC_none, c1b_stepSimC_none]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    exact evalDist_withEagerCoins_step_unused x.1.base.mir
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x)
      (fun res => res.2.1.base.mir) (fun res => G res.1 res.2)
  · dsimp only [stepSimCEager, stepSimCEagerInject]
    rw [c1b_simRecvUsesCoin_none, evictStopsC_none, c1b_stepSimC_none]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    exact evalDist_withEagerCoins_step_unused x.1.base.mir
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x)
      (fun res => res.2.1.base.mir) (fun res => G res.1 res.2)
  · dsimp only [stepSimCEager, stepSimCEagerCorr]
    rw [c1b_stepSimC_none]
    simp only [bind_assoc, pure_bind]
    exact evalDist_withEagerCoins_step_unused x.1.base.mir
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x)
      (fun res => res.2.1.base.mir) (fun res => G res.1 res.2)

private def c1b_pqPres (Inv' : PQ → Prop) {α : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (∀ R, Inv' (sC.base.pq R)) →
    ∀ r ∈ support ((m.run sC).run gh), ∀ R, Inv' (r.1.2.base.pq R)

private theorem c1b_pqPres_pure (Inv' : PQ → Prop) {α : Type} (a : α) :
    c1b_pqPres (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (pure a) := by
  intro sC gh hpq r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1b_pqPres_bind (Inv' : PQ → Prop) {α β : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : c1b_pqPres Inv' m) (hk : ∀ a, c1b_pqPres Inv' (k a)) :
    c1b_pqPres Inv' (m >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  exact hk r₁.1.1 r₁.1.2 r₁.2 (hm sC gh hpq r₁ hr₁) r hr

private theorem c1b_pqPres_get (Inv' : PQ → Prop) :
    c1b_pqPres (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' get := by
  intro sC gh hpq r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1b_pqPres_ite (Inv' : PQ → Prop) {α : Type} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : c1b_pqPres Inv' t) (he : c1b_pqPres Inv' e) :
    c1b_pqPres Inv' (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem c1b_pqPres_liftC (Inv' : PQ → Prop) {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    c1b_pqPres (PQ := PQ) Inv' (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift x >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1b_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨_, _, rfl⟩
  exact hpq

private theorem c1b_pqPres_probe (Inv' : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1b_pqPres (PQ := PQ) Inv'
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1b_probeHook_probe_run] at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hpq

private theorem c1b_pqPres_guardC (Inv' : PQ → Prop) {α : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : c1b_pqPres Inv' m) :
    c1b_pqPres Inv' (guardC m) := by
  unfold guardC
  refine c1b_pqPres_bind Inv' (c1b_pqPres_get Inv') fun sC => ?_
  exact c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' none) hm

private theorem c1b_pqPres_modify_eq (Inv' : PQ → Prop)
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hf : ∀ sC, (f sC).base.pq = sC.base.pq) :
    c1b_pqPres (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (modify f) := by
  intro sC gh hpq r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  simpa [hf sC] using hpq

private theorem c1b_pqPres_zoomB_fwd (Inv' : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1b_pqPres (PQ := PQ) Inv' (runOnBaseState (probeHook fig qepF) (LibsignalSim.fwd Q c')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift ((LibsignalSim.fwd Q c').run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1b_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨p, hp, rfl⟩
  unfold LibsignalSim.fwd at hp
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
  split at hp <;>
    simp only [LibsignalSim.liftQ, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp <;>
    rcases hp with ⟨_, _, rfl⟩ <;>
    exact hpq

private theorem c1b_pq_update_inv {Inv' : PQ → Prop} {pq : Party → PQ} {Q : Party} {pq' : PQ}
    (hpq : ∀ R, Inv' (pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' (Function.update pq Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa using hpq'
  · simpa [Function.update_of_ne hR] using hpq R

private theorem c1b_onAcceptPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq R) := by
  have hupd : ∀ R, Inv' (Function.update s.pq Q pq' R) := c1b_pq_update_inv hpq hpq'
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit Q.other w with
    | none => exact hpq
    | some _ => exact hupd
  · split
    · exact hpq
    · split
      · exact hupd
      · exact hpq

private theorem c1b_onAnswerPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAnswerPure qep Q w isDel ci? T pq' res s).2.pq R) := by
  unfold onAnswerPure
  cases res with
  | none => exact hpq
  | some r =>
    cases r with
    | rejected => exact hpq
    | accepted t i pm =>
      exact c1b_onAcceptPure_pqInv Inv' qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s hpq hpq'

private theorem c1b_pqPres_zoomB_onAccept (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') :
    c1b_pqPres (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF) (LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq').run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1b_probeHook_lift_run, onAccept_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact c1b_onAcceptPure_pqInv Inv' qep Q w isDel t i m ci? T pq' sC.base hpq hpq'

private theorem c1b_pqPres_zoomB_onAnswer (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (hpq' : Inv' pq') :
    c1b_pqPres (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF) (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res)) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1b_probeHook_lift_run, onAnswer_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact c1b_onAnswerPure_pqInv Inv' qep Q w isDel ci? T pq' res sC.base hpq hpq'

private theorem c1b_pqPres_fwdAnswerC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hpq' : Inv' pq') :
    c1b_pqPres Inv' (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine c1b_pqPres_bind Inv' (c1b_pqPres_zoomB_fwd Inv' fig qepF Q c') fun res => ?_
  cases res with
  | none => exact c1b_pqPres_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' none hpq'
  | some r =>
    cases r with
    | rejected =>
      exact c1b_pqPres_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' (some .rejected) hpq'
    | accepted t i pm =>
      refine c1b_pqPres_bind Inv' (c1b_pqPres_modify_eq Inv' _ fun _ => rfl) fun _ => ?_
      exact c1b_pqPres_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' (some (.accepted t i pm)) hpq'

private theorem c1b_pqPres_resyncC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) (hpq' : Inv' pq') :
    c1b_pqPres Inv' (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact c1b_pqPres_pure Inv' _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine c1b_pqPres_bind Inv' (c1b_pqPres_liftC Inv' fig qepF _) fun res => ?_
    cases res with
    | none => exact c1b_pqPres_pure Inv' _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        refine c1b_pqPres_bind Inv' (c1b_pqPres_modify_eq Inv' _ fun _ => rfl) fun _ => ?_
        exact c1b_pqPres_zoomB_onAccept Inv' qep fig qepF Q w true t i pm.2 ci? T pq' hpq'
      | _ => exact c1b_pqPres_pure Inv' _

private theorem c1b_pqPres_fwdC (P : Params PQ PQC) (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) (hpq' : Inv' pq') :
    c1b_pqPres Inv' (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine c1b_pqPres_bind Inv' (c1b_pqPres_get Inv') fun sC => ?_
  cases honestC with
  | none => exact c1b_pqPres_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' c' hpq'
  | some c =>
    refine c1b_pqPres_ite Inv' ?_ (c1b_pqPres_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' c' hpq')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact c1b_pqPres_resyncC Inv' qep fig fs qepF Q w ci? T pq' c r hpq'
    | none =>
      exact c1b_pqPres_bind Inv' (c1b_pqPres_probe Inv' fig qepF Q c') fun _ =>
        c1b_pqPres_pure Inv' _

private theorem c1b_pqPres_fwdEvictC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hpq' : Inv' pq') :
    c1b_pqPres Inv' (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine c1b_pqPres_bind Inv' (c1b_pqPres_get Inv') fun sC => ?_
  refine c1b_pqPres_ite Inv' ?_ (c1b_pqPres_fwdAnswerC Inv' qep fig fs qepF Q w isDel none T pq' c' hpq')
  exact c1b_pqPres_bind Inv' (c1b_pqPres_probe Inv' fig qepF Q c') fun _ => c1b_pqPres_pure Inv' _

private theorem c1b_pqPres_simRecvC (P : Params PQ PQC) (Inv' : PQ → Prop)
    (hrecv : ∀ st msg st' salt, Inv' st → P.spqr.recv st msg = .ok (st', salt) → Inv' st')
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    c1b_pqPres Inv' (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  intro sC gh hpq r hr
  unfold simRecvC at hr
  generalize (2 ^ 32 : ℕ) = maxI at hr
  generalize (25000 : ℕ) = maxSkip at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  have h1 : ∀ {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option (RecvResult (Plain ℓ)))},
      c1b_pqPres Inv' m → r ∈ support ((m.run sC).run gh) → ∀ R, Inv' (r.1.2.base.pq R) :=
    fun hm hrm => hm sC gh hpq r hrm
  refine h1 ?_ hr
  refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
  refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
  refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
  refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact c1b_pqPres_pure Inv' _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
    refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact c1b_pqPres_pure Inv' _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      have hpq' : Inv' pq' := hrecv (sC.base.pq Q) h.pqRatchet pq' salt (hpq Q) hspqr
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
        exact c1b_pqPres_fwdC P Inv' qep fig fs qepF Q w isDel
          (some ci) h.senderRatchetKey pq' _ _ hpq'
      | none =>
        dsimp only
        refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
        refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
        refine c1b_pqPres_ite Inv'
          (c1b_pqPres_bind Inv' (c1b_pqPres_modify_eq Inv' _ fun _ => rfl) fun _ => ?_) ?_ <;>
        · refine c1b_pqPres_ite Inv' (c1b_pqPres_pure Inv' _) ?_
          cases decT h.senderRatchetKey with
          | none => exact c1b_pqPres_pure Inv' _
          | some T =>
            exact c1b_pqPres_ite Inv'
              (c1b_pqPres_fwdEvictC Inv' qep fig fs qepF Q w isDel h.senderRatchetKey pq' _ hpq')
              (c1b_pqPres_fwdC P Inv' qep fig fs qepF Q w isDel
                none h.senderRatchetKey pq' _ _ hpq')

private theorem c1b_pqPres_simCorrC (P : Params PQ PQC) (Inv' : PQ → Prop) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    c1b_pqPres Inv' (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  intro sC gh hpq r hr
  unfold simCorrC at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hcond : sC.base.mir.win || !(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q ||
      !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)
  · simp [hcond] at hr; subst hr; exact hpq
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨⟨ans, sC'⟩, gh'⟩, hp, hr⟩
    have hpq' := c1b_pqPres_liftC Inv' fig qepF (SM.corrQuery Q) sC gh hpq ((ans, sC'), gh') hp
    cases ans with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hpq'
    | some st =>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hpq

private theorem c1b_mkPub_invB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) {q r : ℕ}
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32)
    (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hpq : ∀ R, InvB Inv q r (s.pq R))
    (hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub)) :
    InvB Inv q (r - 1) pq' := by
  unfold LibsignalSim.mkPub at hmk
  rw [Option.map_eq_some_iff] at hmk
  rcases hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  have hpq' : st' = pq' := congrArg Prod.fst hpair
  subst hpq'
  exact InvB.send hS hr (hpq Q) hsend

private theorem c1b_stepSim_send_invB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rc : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, InvB Inv q r (st.1.pq R))
    (z : Option (List (BitVec 8)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hz : z ∈ support (
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
        SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
      (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal rc)).run st.1)).run st.2 >>=
        (fun x => pure (x.1.1, (x.1.2, x.2))))) :
    ∀ R, InvB Inv q (r - 1) (z.2.1.pq R) := by
  have hpq_mono : ∀ R, InvB Inv q (r - 1) (st.1.pq R) := fun R => InvB.mono (by omega) (hpq R)
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  change z ∈ support ((simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal rc)).run st.1)).run st.2 >>=
    (fun x => pure (x.1.1, (x.1.2, x.2)))) at hz
  unfold LibsignalSim.guard LibsignalSim.simSend at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hstop : st.1.stopped
  · simp [hstop] at hz; subst hz; exact hpq_mono
  · simp only [hstop, Bool.false_eq_true, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir] at hz; subst hz; exact hpq_mono
    · simp only [hmir, Bool.false_eq_true, ite_false] at hz
      cases hep : st.1.mir.epMgmt 3 qep Q rc.isSome with
      | none => simp [hep] at hz; subst hz; exact hpq_mono
      | some s₁ =>
        simp only [hep] at hz
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch] at hz; subst hz; exact hpq_mono
        · simp only [hch, Bool.false_eq_true, ite_false] at hz
          cases rc with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨c_cka, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpq_mono
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : InvB Inv q (r - 1) pq' := c1b_mkPub_invB P Inv hS hr st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, InvB Inv q (r - 1) (Function.update st.1.pq Q pq' R) :=
                c1b_pq_update_inv hpq_mono hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_mono
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_mono
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_mono
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_mono
                  · exact hupd
          | none =>
            simp only [pure_bind, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rq, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpq_mono
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : InvB Inv q (r - 1) pq' := c1b_mkPub_invB P Inv hS hr st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, InvB Inv q (r - 1) (Function.update st.1.pq Q pq' R) :=
                c1b_pq_update_inv hpq_mono hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_mono
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_mono
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_mono
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_mono
                  · exact hupd

private theorem c1b_stepSimCNone_invB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q)) :
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x),
      ∀ Q, InvB Inv q (r - 1) (z.2.1.base.pq Q) := by
  intro z hz
  rcases q_sm with ((((⟨Q, m₀, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rw [c1b_stepSimCNone_transmit_eq, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rw [c1b_cxSend_base]
    have hres' : res ∈ support (
        let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
          SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
        (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ none rc)).run x.sim.1)).run x.sim.2 >>=
          (fun y => pure (y.1.1, (y.1.2, y.2)))) := by
      simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres
    exact c1b_stepSim_send_invB P Inv ℓ Dh encPt encT idOf lam qep q r hS hr Q m₀ none rc x.sim hpq res hres'
  · rw [c1b_stepSimCNone_chall_eq, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rw [c1b_cxSend_base]
    have hres' : res ∈ support (
        let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
          SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
        (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ (some m₁) rc)).run x.sim.1)).run x.sim.2 >>=
          (fun y => pure (y.1.1, (y.1.2, y.2)))) := by
      simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres
    exact c1b_stepSim_send_invB P Inv ℓ Dh encPt encT idOf lam qep q r hS hr Q m₀ (some m₁) rc x.sim hpq res hres'
  · dsimp only [stepSimCNone] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    intro R
    exact InvB.mono (by omega)
      (c1b_pqPres_guardC (InvB Inv q r)
        (c1b_pqPres_simRecvC P (InvB Inv q r) (spqrCLocal_closedRecv hS) encT decT qep _ _ (qep + 1) Q w true)
        x.1 x.2 hpq res hres R)
  · dsimp only [stepSimCNone] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    intro R
    exact InvB.mono (by omega)
      (c1b_pqPres_guardC (InvB Inv q r)
        (c1b_pqPres_simRecvC P (InvB Inv q r) (spqrCLocal_closedRecv hS) encT decT qep _ _ (qep + 1) Q w false)
        x.1 x.2 hpq res hres R)
  · dsimp only [stepSimCNone] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    intro R
    exact InvB.mono (by omega)
      (c1b_pqPres_guardC (InvB Inv q r)
        (c1b_pqPres_simCorrC P (InvB Inv q r) encT _ (qep + 1) Dh Q)
        x.1 x.2 hpq res hres R)

private theorem c1b_evalDist_bind_congr_support {α : Type}
    (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact evalDist_bind_congr _ _ _ fun u =>
      ih u fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

private theorem c1b_evalDist_runSimCEager {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (x : JointC PQ Pt ℓ)
    (F : α → JointC PQ Pt ℓ → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q)) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa x ec >>= fun z =>
        F z.1 z.2.1 z.2.2)] =
      𝒟[c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep oa x >>= fun z =>
        withEagerCoins z.2.1.base.mir (F z.1 z.2)] := by
  induction oa using OracleComp.inductionOn generalizing r x with
  | pure a =>
    simp only [runSimCEager_pure, c1b_runSimCNone_pure, pure_bind]
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    rcases t with u | q_sm
    · have hq' : ∀ y, (cont y).IsQueryBoundP p r := fun y => by simpa [hp_inl u] using hq.2 y
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inl_bind, c1b_runSimCNone_inl_bind, bind_assoc]
      rw [evalDist_withEagerCoins_bind_swap x.1.base.mir
        (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _)]
      refine evalDist_bind_congr _ _ _ fun y => ?_
      exact ih y r (hq' y) x hpq
    · have hr : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by
        simpa [hp_inr q_sm] using hq.2 ans
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inr_bind, c1b_runSimCNone_inr_bind, bind_assoc]
      rw [c1b_evalDist_stepSimCEager P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep q_sm x
        (fun ans x' ec' =>
          runSimCEager P ℓ Dh encPt encT decT idOf lam qep none (cont ans) x' ec' >>= fun z =>
          F z.1 z.2.1 z.2.2) hpq (spqrCLocal_total hS hr)]
      refine c1b_evalDist_bind_congr_support _ _ _ fun z hz => ?_
      exact ih z.1 (r - 1) (hq' z.1) z.2
        (c1b_stepSimCNone_invB P Inv ℓ Dh encPt encT decT idOf lam qep q r hS hr q_sm x hpq z hz)

private theorem c1b_evalDist_runSimCNone_eq_withEagerCoins_runSimCEager {α : Type}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (x : JointC PQ Pt ℓ)
    (G : α → JointC PQ Pt ℓ → ProbComp Bool)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q)) :
    𝒟[c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep oa x >>= fun z => G z.1 z.2] =
      𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa x ec >>= fun z =>
        G z.1 z.2.1)] := by
  rw [c1b_evalDist_runSimCEager P Inv ℓ Dh encPt encT decT idOf lam qep q r hS hp_inl hp_inr oa hq x
    (fun a s _ => G a s) hpq]
  refine evalDist_bind_congr _ _ _ fun z => ?_
  exact (evalDist_withEagerCoins_const z.2.1.base.mir (G z.1 z.2)).symm

private theorem c1b_initSimC_invB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) {q : ℕ}
    (hS : SpqrCLocal P.spqr q Inv) (pqrKey : BitVec 256) :
    ∀ Q, InvB Inv q q
      ((initSimC (Pt := Pt) (ℓ := ℓ) (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).base.pq Q) := by
  intro Q
  cases Q <;> simp [initSimC, initSim, InvB.init hS]

/-- Equates `simCNoneWinEvent` to slot `0` of `runWinAtC` from the initial joint state. -/
theorem evalDist_simCNoneWinEvent_eq_eagerC (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : ℕ) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runWinAtC P ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
  intro sm
  rw [c1b_simCNoneWinEvent_eq_runSimCNone]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[c1b_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false) >>= fun z =>
          pure z.2.2.1.win] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAtC P ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
    intro pqrKey
    rw [c1b_evalDist_runSimCNone_eq_withEagerCoins_runSimCEager P Inv ℓ Dh encPt encT decT idOf lam
      qep q q hS (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm (k_root, x₀) b, false)
      (fun _ s => pure s.2.1.win) (c1b_initSimC_invB P Inv hS pqrKey)]
    change 𝒟[withEagerCoins (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).mir _] = _
    rw [evalDist_withEagerCoins_initSim Pt]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

private theorem c1c_stepSimCNone_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hstop : x.1.base.stopped = true) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x = pure (smRangeNone q_sm, x) := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSimCNone, simImplC, guardC, smRangeNone, hstop, StateT.run_bind, StateT.run_get]

private theorem c1c_stepSimC_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hstop : x.1.base.stopped = true) :
    stepSimC P ℓ Dh encPt encT decT idOf lam qep k q_sm x = pure (smRangeNone q_sm, x) := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSimC, simRecvStops, JointC.sim, hstop,
      c1c_stepSimCNone_of_stopped P ℓ Dh encPt encT decT idOf lam qep _ x hstop]

private theorem c1c_stepSimCEager_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hstop : x.1.base.stopped = true) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm x ec =
      (updateAllEagerCoins x.1.base.mir x.1.base.mir (fun _ => false) ec >>= fun ec' =>
        pure (smRangeNone q_sm, (x, ec'))) := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp [stepSimCEager, stepSimCEagerTransmit, stepSimEagerTransmit, JointC.sim, hstop,
      stepSim_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ (x.1.base, x.2.1) hstop,
      smRangeNone, cxSend, bind_assoc]
  · simp [stepSimCEager, stepSimCEagerChall, stepSimEagerChall, JointC.sim, hstop,
      stepSim_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ (x.1.base, x.2.1) hstop,
      smRangeNone, cxSend, bind_assoc]
  · simp [stepSimCEager, stepSimCEagerDeliver, simRecvUsesCoin, JointC.sim, hstop,
      evictStopsC_of_stopped P encT decT k Q w _ x hstop,
      c1c_stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop, smRangeNone]
  · simp [stepSimCEager, stepSimCEagerInject, simRecvUsesCoin, JointC.sim, hstop,
      evictStopsC_of_stopped P encT decT k Q w _ x hstop,
      c1c_stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop, smRangeNone]
  · simp [stepSimCEager, stepSimCEagerCorr,
      c1c_stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop, smRangeNone]

private theorem c1c_evalDist_runSimCEager_stopped {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hstop : x.1.base.stopped = true) :
    𝒟[runSimCEager P ℓ Dh encPt encT decT idOf lam qep k oa x ec >>=
        fun r => pure (r.2.1.1.base.stopped && r.2.1.2.1.win)] =
      𝒟[(pure x.2.1.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing ec with
  | pure a =>
    simp [runSimCEager_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inl_bind, bind_assoc]
      refine (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool)) fun v => ih v ec).trans ?_
      exact OracleComp.evalDist_bind_const _ _
    | inr q_sm =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inr_bind, c1c_stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k q_sm x ec hstop,
        bind_assoc, pure_bind]
      refine (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool)) fun ec' =>
        ih (smRangeNone q_sm) ec').trans ?_
      exact OracleComp.evalDist_bind_const _ _

private theorem c1c_pq_update_inv {PQ : Type} {Inv' : PQ → Prop} {pq : Party → PQ} {Q : Party} {pq' : PQ}
    (hpq : ∀ R, Inv' (pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' (Function.update pq Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa using hpq'
  · simpa [Function.update_of_ne hR] using hpq R

private theorem c1c_mkPub_invB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32)
    (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hpq : ∀ R, InvB Inv q r (s.pq R))
    (hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub)) :
    InvB Inv q (r - 1) pq' := by
  unfold LibsignalSim.mkPub at hmk
  rw [Option.map_eq_some_iff] at hmk
  rcases hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  have hpq' : st' = pq' := congrArg Prod.fst hpair
  subst hpq'
  exact InvB.send hS hr0 (hpq Q) hsend

private theorem c1c_stepSim_send_pqInvB (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_opt : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, InvB Inv q r (st.1.pq R))
    (z : Option (List (BitVec 8)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hz : z ∈ support (
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
        SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
      (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r_opt)).run st.1)).run st.2 >>=
        (fun x => pure (x.1.1, (x.1.2, x.2))))) :
    ∀ R, InvB Inv q (r - 1) (z.2.1.pq R) := by
  have hpq_sub : ∀ R, InvB Inv q (r - 1) (st.1.pq R) := fun R => InvB.mono (by omega) (hpq R)
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  change z ∈ support ((simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r_opt)).run st.1)).run st.2 >>=
    (fun x => pure (x.1.1, (x.1.2, x.2)))) at hz
  unfold LibsignalSim.guard LibsignalSim.simSend at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hstop : st.1.stopped
  · simp [hstop] at hz; subst hz; exact hpq_sub
  · simp only [hstop, Bool.false_eq_true, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir] at hz; subst hz; exact hpq_sub
    · simp only [hmir, Bool.false_eq_true, ite_false] at hz
      cases hep : st.1.mir.epMgmt 3 qep Q r_opt.isSome with
      | none => simp [hep] at hz; subst hz; exact hpq_sub
      | some s₁ =>
        simp only [hep] at hz
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch] at hz; subst hz; exact hpq_sub
        · simp only [hch, Bool.false_eq_true, ite_false] at hz
          cases r_opt with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨c_cka, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpq_sub
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : InvB Inv q (r - 1) pq' := c1c_mkPub_invB P Inv q r hS hr0 st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, InvB Inv q (r - 1) (Function.update st.1.pq Q pq' R) := c1c_pq_update_inv hpq_sub hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_sub
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_sub
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_sub
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_sub
                  · exact hupd
          | none =>
            simp only [pure_bind, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rq, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpq_sub
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : InvB Inv q (r - 1) pq' := c1c_mkPub_invB P Inv q r hS hr0 st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, InvB Inv q (r - 1) (Function.update st.1.pq Q pq' R) := c1c_pq_update_inv hpq_sub hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_sub
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_sub
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq_sub
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq_sub
                  · exact hupd

private theorem c1c_onAcceptPure_stopped {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.stopped = s.stopped := by
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit Q.other w <;> rfl
  · split
    · rfl
    · split <;> rfl

private theorem c1c_onAcceptPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq R) := by
  have hupd : ∀ R, Inv' (Function.update s.pq Q pq' R) := c1c_pq_update_inv hpq hpq'
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit Q.other w with
    | none => exact hpq
    | some _ => exact hupd
  · split
    · exact hpq
    · split
      · exact hupd
      · exact hpq

private theorem c1c_onAnswerPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAnswerPure qep Q w isDel ci? T pq' res s).2.pq R) := by
  unfold onAnswerPure
  cases res with
  | none => exact hpq
  | some r =>
    cases r with
    | rejected => exact hpq
    | accepted t i pm =>
      exact c1c_onAcceptPure_pqInv Inv' qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s hpq hpq'

private def c1c_preserves {α : Type} (Inv' : PQ → Prop)
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (∀ R, Inv' (sC.base.pq R)) →
    ∀ r ∈ support ((m.run sC).run gh),
      r.1.2.base.stopped = sC.base.stopped ∧ ∀ R, Inv' (r.1.2.base.pq R)

private theorem c1c_preserves_pure {α : Type} (Inv' : PQ → Prop) (a : α) :
    c1c_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (pure a) := by
  intro sC gh hpq r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem c1c_preserves_bind {α β : Type} {Inv' : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : c1c_preserves Inv' m) (hk : ∀ a, c1c_preserves Inv' (k a)) :
    c1c_preserves Inv' (m >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  obtain ⟨hstop₁, hpq₁⟩ := hm sC gh hpq r₁ hr₁
  obtain ⟨hstop₂, hpq₂⟩ := hk r₁.1.1 r₁.1.2 r₁.2 hpq₁ r hr
  exact ⟨hstop₂.trans hstop₁, hpq₂⟩

private theorem c1c_preserves_get (Inv' : PQ → Prop) :
    c1c_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' get := by
  intro sC gh hpq r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem c1c_preserves_ite {α : Type} {Inv' : PQ → Prop} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : c1c_preserves Inv' t) (he : c1c_preserves Inv' e) :
    c1c_preserves Inv' (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem c1c_preserves_modify (Inv' : PQ → Prop)
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hf : ∀ sC, (f sC).base.stopped = sC.base.stopped ∧ (f sC).base.pq = sC.base.pq) :
    c1c_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (modify f) := by
  intro sC gh hpq r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := hf sC
  refine ⟨h1, ?_⟩
  rw [h2]
  exact hpq

private theorem c1c_probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (y : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift y).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) y).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

private theorem c1c_probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem c1c_preserves_liftC {α : Type} (Inv' : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    c1c_preserves (PQ := PQ) Inv' (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift x >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1c_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨_, _, rfl⟩
  exact ⟨rfl, hpq⟩

private theorem c1c_preserves_probe (Inv' : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1c_preserves (PQ := PQ) Inv'
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1c_probeHook_probe_run] at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem c1c_preserves_get_bind {α : Type} {Inv' : PQ → Prop}
    {k : LibsignalToModularSchemeSimState PQ Pt ℓ → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (hk : ∀ sC, (∀ R, Inv' (sC.base.pq R)) → c1c_preserves Inv' (k sC)) :
    c1c_preserves Inv' (get >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind] at hr
  exact hk sC hpq sC gh hpq r hr

private theorem c1c_preserves_zoomB_fwd (Inv' : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    c1c_preserves (PQ := PQ) Inv' (runOnBaseState (probeHook fig qepF) (LibsignalSim.fwd Q c')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift ((LibsignalSim.fwd Q c').run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  have hfwd : (LibsignalSim.fwd Q c').run sC.base = (LibsignalSim.fwd Q c' >>= pure).run sC.base := by simp
  rw [hfwd, StateT.run_bind, c1c_probeHook_lift_run] at hr
  dsimp only [fig8ImplH1] at hr
  rw [simulateQ_fwd_run fig 3 qepF SM.Config.h1 Q c' pure sC.base gh.1] at hr
  simp only [StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem c1c_preserves_zoomB_onAnswer (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq')
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :
    c1c_preserves (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF) (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res)) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1c_probeHook_lift_run, onAnswer_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨onAnswerPure_stopped qep Q w isDel ci? T pq' res sC.base,
    c1c_onAnswerPure_pqInv Inv' qep Q w isDel ci? T pq' res sC.base hpq hpq'⟩

private theorem c1c_preserves_zoomB_onAccept (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') :
    c1c_preserves (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF) (LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq').run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, c1c_probeHook_lift_run, onAccept_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨c1c_onAcceptPure_stopped qep Q w isDel t i m ci? T pq' sC.base,
    c1c_onAcceptPure_pqInv Inv' qep Q w isDel t i m ci? T pq' sC.base hpq hpq'⟩

private theorem c1c_preserves_fwdAnswerC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (c' : Fig8C Pt) :
    c1c_preserves Inv' (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine c1c_preserves_bind (c1c_preserves_zoomB_fwd Inv' fig qepF Q c') fun res => ?_
  cases res with
  | none => exact c1c_preserves_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' none
  | some r =>
    cases r with
    | rejected => exact c1c_preserves_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' (some .rejected)
    | accepted t i pm =>
      refine c1c_preserves_bind (c1c_preserves_modify Inv' _ (fun _ => ⟨rfl, rfl⟩)) fun _ => ?_
      exact c1c_preserves_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' (some (.accepted t i pm))

private theorem c1c_preserves_resyncC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (hpq' : Inv' pq') (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    c1c_preserves Inv' (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact c1c_preserves_pure Inv' _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine c1c_preserves_bind (c1c_preserves_liftC Inv' fig qepF _) fun res => ?_
    cases res with
    | none => exact c1c_preserves_pure Inv' _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        refine c1c_preserves_bind (c1c_preserves_modify Inv' _ (fun _ => ⟨rfl, rfl⟩)) fun _ => ?_
        exact c1c_preserves_zoomB_onAccept Inv' qep fig qepF Q w true t i pm.2 ci? T pq' hpq'
      | _ => exact c1c_preserves_pure Inv' _

private theorem c1c_preserves_fwdC (P : Params PQ PQC) (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    c1c_preserves Inv' (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine c1c_preserves_bind (c1c_preserves_get Inv') fun sC => ?_
  cases honestC with
  | none => exact c1c_preserves_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' hpq' c'
  | some c =>
    refine c1c_preserves_ite ?_ (c1c_preserves_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' hpq' c')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact c1c_preserves_resyncC Inv' qep fig fs qepF Q w ci? T pq' hpq' c r
    | none =>
      exact c1c_preserves_bind (c1c_preserves_probe Inv' fig qepF Q c') fun _ =>
        c1c_preserves_pure Inv' _

private theorem c1c_preserves_fwdEvictC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (c' : Fig8C Pt) :
    c1c_preserves Inv' (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine c1c_preserves_bind (c1c_preserves_get Inv') fun sC => ?_
  refine c1c_preserves_ite ?_ (c1c_preserves_fwdAnswerC Inv' qep fig fs qepF Q w isDel none T pq' hpq' c')
  exact c1c_preserves_bind (c1c_preserves_probe Inv' fig qepF Q c') fun _ =>
    c1c_preserves_pure Inv' _

private theorem c1c_preserves_simRecvC (P : Params PQ PQC) (Inv' : PQ → Prop)
    (hrecv : ∀ st msg st' salt, Inv' st → P.spqr.recv st msg = .ok (st', salt) → Inv' st')
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    c1c_preserves Inv' (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine c1c_preserves_get_bind fun sC hpq => ?_
  dsimp only
  refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
  refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
  refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
  refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact c1c_preserves_pure Inv' _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
    refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact c1c_preserves_pure Inv' _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      have hpq' : Inv' pq' := hrecv (sC.base.pq Q) h.pqRatchet pq' salt (hpq Q) hspqr
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
        exact c1c_preserves_fwdC P Inv' qep fig fs qepF Q w isDel
          (some ci) h.senderRatchetKey pq' hpq' _ _
      | none =>
        dsimp only
        refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
        refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
        refine c1c_preserves_ite
          (c1c_preserves_bind (c1c_preserves_modify Inv' _ (fun _ => ⟨rfl, rfl⟩)) fun _ => ?_) ?_ <;>
        · refine c1c_preserves_ite (c1c_preserves_pure Inv' _) ?_
          cases decT h.senderRatchetKey with
          | none => exact c1c_preserves_pure Inv' _
          | some T =>
            exact c1c_preserves_ite
              (c1c_preserves_fwdEvictC Inv' qep fig fs qepF Q w isDel h.senderRatchetKey pq' hpq' _)
              (c1c_preserves_fwdC P Inv' qep fig fs qepF Q w isDel
                none h.senderRatchetKey pq' hpq' _ _)

private theorem c1c_liftC_bind_run {α β : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α)
    (k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (LibsignalSimC.liftC (probeHook fig qepF) x >>= k).run sC =
      ((probeHook fig qepF).lift x >>= fun a => (k a).run sC) := by
  change ((probeHook fig qepF).lift x >>= fun a => pure (a, sC)) >>= (fun p => (k p.1).run p.2) = _
  simp only [bind_assoc, pure_bind]

private theorem c1c_preserves_simCorrC (P : Params PQ PQC) (Inv' : PQ → Prop)
    (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    c1c_preserves Inv' (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  intro sC gh hpq r hr
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hr
  dsimp only at hr
  split at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨rfl, hpq⟩
  · rw [c1c_liftC_bind_run, StateT.run_bind] at hr
    simp only [MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨r_opt, gh'⟩, _, hr⟩
    cases r_opt with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨rfl, hpq⟩
    | some st =>
      dsimp only at hr
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨rfl, hpq⟩

private theorem c1c_preserves_guardC {α : Type} {Inv' : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : c1c_preserves Inv' m) :
    c1c_preserves Inv' (guardC m) := by
  unfold guardC
  refine c1c_preserves_bind (c1c_preserves_get Inv') fun sC => ?_
  exact c1c_preserves_ite (c1c_preserves_pure Inv' none) hm

private theorem c1c_stepSimCNone_recv_preserve (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (x : JointC PQ Pt ℓ) (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    let q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain :=
      if isDel then .inl (.inl (.inr (Q, w))) else .inl (.inr (Q, w))
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x),
      z.2.1.base.stopped = x.1.base.stopped ∧ ∀ R, InvB Inv q (r - 1) (z.2.1.base.pq R) := by
  intro q_sm z hz
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨res, hres, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hpres : c1c_preserves (InvB Inv q r)
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh (.inr q_sm)) := by
    cases isDel <;>
      exact c1c_preserves_guardC
        (c1c_preserves_simRecvC P (InvB Inv q r) (spqrCLocal_closedRecv hS) encT decT qep _ _ (qep + 1) Q w _)
  obtain ⟨hstop', hpq'⟩ := hpres x.1 x.2 hpq res hres
  exact ⟨hstop', fun R => InvB.mono (by omega) (hpq' R)⟩

private theorem c1c_stepSimCNone_corr_preserve (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (Q : Party) (x : JointC PQ Pt ℓ) (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x),
      z.2.1.base.stopped = x.1.base.stopped ∧ ∀ R, InvB Inv q (r - 1) (z.2.1.base.pq R) := by
  intro z hz
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨res, hres, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hpres : c1c_preserves (InvB Inv q r)
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh (.inr (.inr Q))) :=
    c1c_preserves_guardC (c1c_preserves_simCorrC P (InvB Inv q r) encT _ (qep + 1) Dh Q)
  obtain ⟨hstop', hpq'⟩ := hpres x.1 x.2 hpq res hres
  exact ⟨hstop', fun R => InvB.mono (by omega) (hpq' R)⟩

private theorem c1c_cxSend_base (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q sC s' res).base = s' := by
  cases res <;> rfl

private theorem c1c_runSimCEager_some_stopped_and_win_prob_le {α : Type}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (x : JointC PQ Pt ℓ)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q))
    (hstop : x.1.base.stopped = false) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) oa x ec >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  induction oa using OracleComp.inductionOn generalizing r x with
  | pure a =>
    simp only [runSimCEager_pure, pure_bind, hstop, Bool.false_and]
    rw [evalDist_withEagerCoins_const]
    simp
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    cases t with
    | inl u =>
      have hq' : ∀ v, (cont v).IsQueryBoundP p r := fun v => by simpa [hp_inl u] using hq.2 v
      have hswap :
          𝒟[withEagerCoins x.1.base.mir (fun ec =>
            runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j)
              (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont) x ec >>=
            fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] =
          𝒟[(liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun v =>
            withEagerCoins x.1.base.mir (fun ec =>
              runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont v) x ec >>=
              fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] := by
        simp only [runSimCEager_inl_bind, bind_assoc]
        exact evalDist_withEagerCoins_bind_swap x.1.base.mir
          (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) _
      rw [hswap]
      exact evalDist_bind_true_le_of_support _ _ _ fun v _ => ih v r (hq' v) x hpq hstop
    | inr q_sm =>
      have hr0 : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by
        simpa [hp_inr q_sm] using hq.2 ans
      have hW0 : Corr.SpqrSendTotalOn P.spqr (InvB Inv q r) := spqrCLocal_total hS hr0
      have hrecv : ∀ (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
          (stepC : ProbComp (Option (SM.RecvResult (Plain ℓ)) × JointC PQ Pt ℓ))
          (hstepC_stops : simRecvUsesCoin P encT decT (some j) Q w isDel x.sim = false →
            simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim = true →
            stepC = pure (
              let r₀ := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel 0 x.sim
              (r₀.1, x.withSim r₀.2)))
          (hstepC_nostops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim = false →
            ∀ z ∈ support stepC,
              z.2.1.base.stopped = x.1.base.stopped ∧ ∀ R, InvB Inv q (r - 1) (z.2.1.base.pq R))
          (cont' : Option (SM.RecvResult (Plain ℓ)) →
            SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
          (hq_recv : ∀ u, (cont' u).IsQueryBoundP p (r - 1))
          (ih' : ∀ u (r' : ℕ),
            (cont' u).IsQueryBoundP p r' →
            ∀ (x' : JointC PQ Pt ℓ),
              (∀ Q, InvB Inv q r' (x'.1.base.pq Q)) →
              x'.1.base.stopped = false →
              𝒟[withEagerCoins x'.1.base.mir (fun ec =>
                  runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' u) x' ec >>=
                    fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] {true} ≤
                spurUnitPt P.C.F encPt Dh),
          𝒟[withEagerCoins x.1.base.mir (fun ec =>
              ((if simRecvUsesCoin P encT decT (some j) Q w isDel x.sim && !recvPanicsW P Q w x.1.base then
                let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel (ec Q) x.sim
                updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
                pure (res.1, (x.withSim res.2, ec'))
              else if evictStopsC P encT decT (some j) Q w isDel x then
                let res := evictStopStepC P Dh encPt decT Q w (ec Q) x
                updateAllEagerCoins x.1.base.mir res.2.1.base.mir (· == Q) ec >>= fun ec' =>
                pure (res.1, (res.2, ec'))
              else
                stepC >>= fun res =>
                updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
                pure (res.1, (res.2, ec'))) >>= fun res =>
                runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' res.1) res.2.1 res.2.2) >>=
                  fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] {true} ≤
            spurUnitPt P.C.F encPt Dh := by
        intro Q w isDel stepC hstepC_stops hstepC_nostops cont' hq_recv ih'
        by_cases huse' : (simRecvUsesCoin P encT decT (some j) Q w isDel x.sim &&
            !recvPanicsW P Q w x.1.base) = true
        · have huse : simRecvUsesCoin P encT decT (some j) Q w isDel x.sim = true :=
            by simp only [Bool.and_eq_true] at huse'; exact huse'.1
          simp only [huse', ↓reduceIte, bind_assoc, pure_bind]
          have hinw := inWin_of_simRecvUsesCoin P encT decT (some j) Q w isDel x.sim huse
          have hused :
              𝒟[withEagerCoins x.1.base.mir (fun ec =>
                let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel (ec Q) x.sim
                updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
                runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' res.1) (x.withSim res.2) ec' >>=
                  fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] =
              𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim
                withEagerCoins (x.withSim res.2).1.base.mir (fun ec' =>
                  runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' res.1) (x.withSim res.2) ec' >>=
                    fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] := by
            have h0 := evalDist_withEagerCoins_step_used Q x.1.base.mir hinw (pure ())
              (fun _ c_cka =>
                let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim
                (res.1, x.withSim res.2))
              (fun r => r.2.1.base.mir)
              (fun r ec' =>
                runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' r.1) r.2 ec' >>=
                  fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))
            simp only [pure_bind] at h0
            exact h0
          rw [hused]
          have hcongr :
              𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim
                withEagerCoins (x.withSim res.2).1.base.mir (fun ec' =>
                  runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' res.1) (x.withSim res.2) ec' >>=
                    fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] =
              𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                pure (spurPtStep P Dh encPt decT Q w isDel c_cka x.sim)] := by
            refine evalDist_bind_congr _ _ _ fun c_cka => ?_
            have hsw := simRecvStep_stopped_iff_and_win P ℓ Dh encPt encT decT idOf lam qep
              (some j) Q w isDel c_cka x.sim hstop
            have hst' : (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim).2.1.stopped = true :=
              hsw.1 huse
            have hwin' : (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim).2.2.win =
                spurPtStep P Dh encPt decT Q w isDel c_cka x.sim := by
              simp [hsw.2 hst', huse]
            have hstopC : (x.withSim (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim).2).1.base.stopped = true :=
              hst'
            have h1 :
                𝒟[withEagerCoins (x.withSim (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim).2).1.base.mir
                  (fun ec' =>
                    runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j)
                      (cont' (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim).1)
                      (x.withSim (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim).2) ec' >>=
                      fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] =
                𝒟[withEagerCoins (x.withSim (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim).2).1.base.mir
                  (fun _ => pure (spurPtStep P Dh encPt decT Q w isDel c_cka x.sim))] := by
              unfold withEagerCoins
              refine evalDist_bind_congr _ _ _ fun cA => evalDist_bind_congr _ _ _ fun cB => ?_
              rw [c1c_evalDist_runSimCEager_stopped P ℓ Dh encPt encT decT idOf lam qep (some j) _ _ _ hstopC]
              simp [JointC.withSim, hwin']
            rw [h1, evalDist_withEagerCoins_const]
          rw [hcongr]
          exact spurPtStep_prob_le P Dh encPt decT Q w isDel x.sim
        · have huse_f' : (simRecvUsesCoin P encT decT (some j) Q w isDel x.sim &&
              !recvPanicsW P Q w x.1.base) = false :=
            Bool.eq_false_iff.mpr huse'
          by_cases hev : evictStopsC P encT decT (some j) Q w isDel x = true
          ·
            simp only [huse_f', hev, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
            have hinw := inWin_of_evictStopsC P encT decT (some j) Q w isDel x hev
            have h0 := evalDist_withEagerCoins_step_used Q x.1.base.mir hinw (pure ())
              (fun _ c_cka => evictStopStepC P Dh encPt decT Q w c_cka x)
              (fun r => r.2.1.base.mir)
              (fun r ec' =>
                runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' r.1) r.2 ec' >>=
                  fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))
            simp only [pure_bind] at h0
            rw [h0]
            have hcongr :
                𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                  withEagerCoins (evictStopStepC P Dh encPt decT Q w c_cka x).2.1.base.mir (fun ec' =>
                    runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j)
                      (cont' (evictStopStepC P Dh encPt decT Q w c_cka x).1)
                      (evictStopStepC P Dh encPt decT Q w c_cka x).2 ec' >>=
                      fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] =
                𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                  pure (spurPtStep P Dh encPt decT Q w false c_cka x.sim)] := by
              refine evalDist_bind_congr _ _ _ fun c_cka => ?_
              have hstopC : (evictStopStepC P Dh encPt decT Q w c_cka x).2.1.base.stopped = true := rfl
              have h1 :
                  𝒟[withEagerCoins (evictStopStepC P Dh encPt decT Q w c_cka x).2.1.base.mir (fun ec' =>
                    runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j)
                      (cont' (evictStopStepC P Dh encPt decT Q w c_cka x).1)
                      (evictStopStepC P Dh encPt decT Q w c_cka x).2 ec' >>=
                      fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] =
                  𝒟[withEagerCoins (evictStopStepC P Dh encPt decT Q w c_cka x).2.1.base.mir
                    (fun _ => pure (spurPtStep P Dh encPt decT Q w false c_cka x.sim))] := by
                unfold withEagerCoins
                refine evalDist_bind_congr _ _ _ fun cA => evalDist_bind_congr _ _ _ fun cB => ?_
                rw [c1c_evalDist_runSimCEager_stopped P ℓ Dh encPt encT decT idOf lam qep (some j) _ _ _ hstopC]
                simp [evictStopStepC]
              rw [h1, evalDist_withEagerCoins_const]
            rw [hcongr]
            exact spurPtStep_prob_le P Dh encPt decT Q w false x.sim
          have hev_f : evictStopsC P encT decT (some j) Q w isDel x = false :=
            Bool.eq_false_iff.mpr hev
          simp only [huse_f', hev_f, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          rw [evalDist_withEagerCoins_step_unused x.1.base.mir stepC
            (fun res => res.2.1.base.mir)
            (fun res ec' =>
              runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' res.1) res.2 ec' >>=
                fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))]
          by_cases hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim = true
          · have hnpW : recvPanicsW P Q w x.1.base = false :=
              recvPanicsW_eq_false_of_simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w
                isDel x.sim hstops
            have huse_f : simRecvUsesCoin P encT decT (some j) Q w isDel x.sim = false := by
              rw [hnpW, Bool.not_false, Bool.and_true] at huse_f'
              exact huse_f'
            rw [hstepC_stops huse_f hstops, pure_bind]
            set r₀ := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel 0 x.sim
            have hst' : r₀.2.1.stopped = true := by
              rw [simRecvStops_eq_of_not_recvPanicsW P ℓ Dh encPt encT decT idOf lam qep (some j) Q w
                isDel x.sim hnpW hstop] at hstops
              exact hstops
            have hsw := simRecvStep_stopped_iff_and_win P ℓ Dh encPt encT decT idOf lam qep
              (some j) Q w isDel 0 x.sim hstop
            have hwin' : r₀.2.2.win = false := by
              have h2 := hsw.2 hst'
              simp [huse_f] at h2
              exact h2
            have hstopC : (x.withSim r₀.2).1.base.stopped = true := hst'
            have h1 :
                𝒟[withEagerCoins (x.withSim r₀.2).1.base.mir (fun ec' =>
                  runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' r₀.1) (x.withSim r₀.2) ec' >>=
                    fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] =
                𝒟[withEagerCoins (x.withSim r₀.2).1.base.mir (fun _ => pure false)] := by
              unfold withEagerCoins
              refine evalDist_bind_congr _ _ _ fun cA => evalDist_bind_congr _ _ _ fun cB => ?_
              rw [c1c_evalDist_runSimCEager_stopped P ℓ Dh encPt encT decT idOf lam qep (some j) _ _ _ hstopC]
              simp [JointC.withSim, hwin']
            rw [h1, evalDist_withEagerCoins_const]
            simp
          · have hstops_f : simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim = false :=
              Bool.eq_false_iff.mpr hstops
            refine evalDist_bind_true_le_of_support _ _ _ fun res hres => ?_
            obtain ⟨hstop', hpq'⟩ := hstepC_nostops hstops_f res hres
            exact ih' res.1 (r - 1) (hq_recv res.1) res.2 hpq' (hstop'.trans hstop)
      rcases q_sm with ((((⟨Q, m₀, r_opt⟩ | ⟨Q, m₀, m₁, r_opt⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · simp only [runSimCEager_inr_bind, stepSimCEager, stepSimCEagerTransmit, bind_assoc, pure_bind]
        have htr := evalDist_stepSimEagerTransmitW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep (some j)
          Q m₀ r_opt x.sim
          (fun ans st' ec' =>
            runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont ans)
              (cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2) ec' >>=
              fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))
          hpq hW0
        change 𝒟[withEagerCoins x.sim.1.mir _] {true} ≤ _
        rw [htr]
        refine evalDist_bind_true_le_of_support _ _ _ fun res hres => ?_
        have hres' : res ∈ support (
            let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
            let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
                (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
              SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
            (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ none r_opt)).run x.sim.1)).run x.sim.2 >>=
              (fun y => pure (y.1.1, (y.1.2, y.2)))) := by
          simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres
        have hstop' : (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1).base.stopped = false := by
          rw [c1c_cxSend_base]
          exact (stepSim_send_stopped P ℓ Dh encPt encT idOf lam qep Q m₀ none r_opt x.sim res hres').trans hstop
        have hpq' : ∀ R, InvB Inv q (r - 1) ((cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1).base.pq R) := by
          rw [c1c_cxSend_base]
          exact c1c_stepSim_send_pqInvB P Inv ℓ Dh encPt encT idOf lam qep q r hS hr0 Q m₀ none r_opt x.sim hpq res hres'
        have hmir' : res.2.1.mir = (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1).base.mir := by
          rw [c1c_cxSend_base]
        rw [hmir']
        exact ih res.1 (r - 1) (hq' res.1) (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2) hpq' hstop'
      · simp only [runSimCEager_inr_bind, stepSimCEager, stepSimCEagerChall, bind_assoc, pure_bind]
        have hch := evalDist_stepSimEagerChallW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep (some j)
          Q m₀ m₁ r_opt x.sim
          (fun ans st' ec' =>
            runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont ans)
              (cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2) ec' >>=
              fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))
          hpq hW0
        change 𝒟[withEagerCoins x.sim.1.mir _] {true} ≤ _
        rw [hch]
        refine evalDist_bind_true_le_of_support _ _ _ fun res hres => ?_
        have hres' : res ∈ support (
            let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
            let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
                (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
              SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
            (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ (some m₁) r_opt)).run x.sim.1)).run x.sim.2 >>=
              (fun y => pure (y.1.1, (y.1.2, y.2)))) := by
          simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres
        have hstop' : (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1).base.stopped = false := by
          rw [c1c_cxSend_base]
          exact (stepSim_send_stopped P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r_opt x.sim res hres').trans hstop
        have hpq' : ∀ R, InvB Inv q (r - 1) ((cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1).base.pq R) := by
          rw [c1c_cxSend_base]
          exact c1c_stepSim_send_pqInvB P Inv ℓ Dh encPt encT idOf lam qep q r hS hr0 Q m₀ (some m₁) r_opt x.sim hpq res hres'
        have hmir' : res.2.1.mir = (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1).base.mir := by
          rw [c1c_cxSend_base]
        rw [hmir']
        exact ih res.1 (r - 1) (hq' res.1) (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2) hpq' hstop'
      · simp only [runSimCEager_inr_bind, stepSimCEager, stepSimCEagerDeliver]
        exact hrecv Q w true
          (stepSimC P ℓ Dh encPt encT decT idOf lam qep (some j) (.inl (.inl (.inr (Q, w)))) x)
          (fun huse_f hstops => by simp [stepSimC, hstops, stepSim_deliver_eq, huse_f])
          (fun hstops_f z hz => by
            simp only [stepSimC, hstops_f, Bool.false_eq_true, ↓reduceIte] at hz
            exact c1c_stepSimCNone_recv_preserve P Inv ℓ Dh encPt encT decT idOf lam qep q r hS Q w true x hpq z hz)
          cont hq' (fun u r' hq'' x' hpq' hstop' => ih u r' hq'' x' hpq' hstop')
      · simp only [runSimCEager_inr_bind, stepSimCEager, stepSimCEagerInject]
        exact hrecv Q w false
          (stepSimC P ℓ Dh encPt encT decT idOf lam qep (some j) (.inl (.inr (Q, w))) x)
          (fun huse_f hstops => by simp [stepSimC, hstops, stepSim_inject_eq, huse_f])
          (fun hstops_f z hz => by
            simp only [stepSimC, hstops_f, Bool.false_eq_true, ↓reduceIte] at hz
            exact c1c_stepSimCNone_recv_preserve P Inv ℓ Dh encPt encT decT idOf lam qep q r hS Q w false x hpq z hz)
          cont hq' (fun u r' hq'' x' hpq' hstop' => ih u r' hq'' x' hpq' hstop')
      · simp only [runSimCEager_inr_bind, stepSimCEager, stepSimCEagerCorr, bind_assoc, pure_bind]
        rw [evalDist_withEagerCoins_step_unused x.1.base.mir
          (stepSimC P ℓ Dh encPt encT decT idOf lam qep (some j) (.inr Q) x)
          (fun res => res.2.1.base.mir)
          (fun res ec' =>
            runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) (cont res.1) res.2 ec' >>=
              fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))]
        refine evalDist_bind_true_le_of_support _ _ _ fun res hres => ?_
        obtain ⟨hstop', hpq'⟩ := c1c_stepSimCNone_corr_preserve P Inv ℓ Dh encPt encT decT idOf lam
          qep q r Q x hpq res hres
        exact ih res.1 (r - 1) (hq' res.1) res.2 hpq' (hstop'.trans hstop)

/-- Bounds slot `j + 1` of `runWinAtC` from the initial joint state by `spurUnitPt`. -/
theorem evalDist_runWinAtC_succ_init_leC (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ)
    (q : ℕ) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runWinAtC P ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
          (fun _ => false) (j + 1)] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  intro sm
  refine evalDist_bind_true_le_of_support _ _ _ fun b _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun k_root _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun x₀ _ => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine evalDist_bind_true_le_of_support _ _ _ fun pqrKey _ => ?_
  let x_init : JointC PQ Pt ℓ :=
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
     SM.initState sm (k_root, x₀) b, false)
  have h1 :
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAtC P ℓ Dh encPt encT decT idOf lam qep A x_init
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) (j + 1)] =
      𝒟[withEagerCoins x_init.1.base.mir (fun ec =>
          runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) A x_init ec >>=
            fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win))] := rfl
  rw [h1]
  have hpq : ∀ Q, InvB Inv q q (x_init.1.base.pq Q) := by
    intro Q
    cases Q
    · simpa [x_init, initSimC, initSim] using InvB.init hS .a2b pqrKey
    · simpa [x_init, initSimC, initSim] using InvB.init hS .b2a pqrKey
  exact c1c_runSimCEager_some_stopped_and_win_prob_le P Inv ℓ Dh encPt encT decT idOf lam qep j q q
    hS (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq x_init hpq rfl

/-- Equates `hiddenSaltGame` to `runHidC` from the initial joint state. -/
theorem evalDist_hiddenSaltGame_eq_eagerC (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : ℕ) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[hiddenSaltGame P ℓ Dh encPt encT decT idOf lam qep A] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runHidC P ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (fun Q => match Q with | .A => eA₀ | .B => 0)] := by
  intro sm
  rw [c1a_hiddenSaltGame_eq_runSimCNone]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[c1a_runSimCNone P ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false) >>= fun z =>
          pure z.2.2.2] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runHidC P ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (fun Q => match Q with | .A => eA₀ | .B => 0)] := by
    intro pqrKey
    unfold runHidC
    rw [c1a_evalDist_runSimCNone_eq_withEagerCoins_runSimCEager P Inv ℓ Dh encPt encT decT idOf lam
      qep q A hq hS
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
       SM.initState sm (k_root, x₀) b, false)
      (fun _ s => pure s.2.2)
      (c1a_initSimC_pqInvB P Inv q hS pqrKey)]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

/-- Establishes `SimInvCX` on the initial joint state. -/
theorem simInvCX_init (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (b : Bool) (k_root x₀ eA₀ pqrKey : BitVec 256)
    (hcoll0 : Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base)
    (hS : SpqrCLocal P.spqr q Inv) :
    let sm_R := libsignalSessionScheme P ℓ encPt lam
    let sm_fig8 := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let s_R := SM.initState sm_R.sendPart (k_root, x₀, eA₀, pqrKey) b
    let sC : LibsignalToModularSchemeSimState PQ Pt ℓ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let s_fig8 := SM.initState sm_fig8 (k_root, x₀) b
    let ec : Party → BitVec 256 := fun Q => match Q with | .A => eA₀ | .B => 0
    let epExp : ℕ → BitVec 256 := fun t => if t = 0 then x₀ else if t = 1 then eA₀ else 0
    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q q x₀ s_R sC s_fig8 ec (fun _ => false) epExp := by
  intro sm_R sm_fig8 s_R sC s_fig8 ec epExp
  have hT : Corr.SpqrInvClosed P.spqr (fun _ => True) :=
    ⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩
  have h := simInvW_init P (fun _ => True) ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀ pqrKey
    hcoll0 hT
  refine ⟨h.toC.mono fun Q => ?_, ?_, ?_, ?_, ?_⟩
  · cases Q
    · simpa [sC, initSimC, initSim] using InvB.init hS .a2b pqrKey
    · simpa [sC, initSimC, initSim] using InvB.init hS .b2a pqrKey
  · intro wc₁ hwc₁
    exact absurd hwc₁ (by simp [sC, initSimC, initSim])
  · refine ⟨fun Q st hst => ?_, fun Q t v hfull hrs => ?_, fun Q t => ?_⟩
    · simp [sC, initSimC, Kept.unknown] at hst
    · simp [sC, initSimC, Kept.unknown] at hrs
    · cases Q <;> by_cases ht : t = 0 <;>
        simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, ht, Party.sendsIn]
  · intro wc hwc
    exact absurd hwc (by simp [sC, initSimC, initSim])
  · intro _
    refine ⟨fun _ => (rootKdf P.C.F k_root (encPt lam)).2,
      fun _ => (rootKdf P.C.F k_root (encPt lam)).1, ?_⟩
    refine ⟨fun wc hwc => absurd hwc (by simp [sC, initSimC, initSim]),
      fun wc hwc => absurd hwc (by simp [sC, initSimC, initSim]),
      fun e he => absurd he (by simp [sC, initSimC]), fun R t v hv => ?_, fun R v hv hR => ?_,
      fun R hR => ?_, fun R hR hsR => ?_, fun R => ?_, fun R hsR => ?_,
      fun e he => absurd he (by simp [sC, initSimC]),
      fun R => ?_, fun R hsR => ?_, fun e he => ?_,
      fun snap hsnap => absurd hsnap (by simp [sC, initSimC])⟩
    · cases R <;> by_cases ht : t = 0 <;>
        simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, ht, Ratchet.rootPRNG, lFS,
          FSAEAD.fromAEADPRG] at hv
      subst hv
      simp [RecvAgrees, lChainAt]
    · cases R <;>
        simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, Ratchet.rootPRNG, lFS,
          FSAEAD.fromAEADPRG] at hv
      subst hv
      simp [SendAgrees, lChainAt]
    · cases R <;> simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, Party.other] at hR
    · cases R <;>
        simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, Party.other, Party.sendsIn,
          dhScheme] at hsR ⊢
    · cases R <;> simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, Party.other]
    · cases R <;>
        simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, Party.sendsIn] at hsR ⊢
    · cases R <;> simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, Ratchet.rootPRNG]
    · cases R <;>
        simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty, Party.sendsIn, epExp,
          dhScheme] at hsR ⊢
    · simp [s_fig8, sm_fig8, SM.initState, lFig8, scheme, initParty] at he

end CryptoGames.LibsignalSM.Proofs.Refinement
