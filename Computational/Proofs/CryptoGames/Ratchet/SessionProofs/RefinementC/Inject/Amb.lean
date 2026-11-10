/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling

/-!
# Ambiguous-receive inject helpers

Stopped-step and invariant-preservation lemmas for the ambiguous-receive subcases of `closeByStateC_inject_step`.
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
set_option autoImplicit false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## Stopped-step lemmas -/

theorem guardC_of_stopped {α : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (hstop : sC.base.stopped = true) :
    ((guardC m).run sC).run gh = pure ((none, sC), gh) := by
  unfold guardC
  change ((get >>= fun s : LibsignalToModularSchemeSimState PQ Pt ℓ =>
    if s.base.stopped = true then pure none else m).run sC).run gh = _
  rw [StateT.run_bind]
  simp [hstop, StateT.run_get, StateT.run_pure]

theorem stepSimCNone_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ)
    (hstop : x.1.base.stopped = true) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x = pure (smRangeNone q, x) := by
  unfold stepSimCNone
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    (dsimp only [simImplC, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim];
     rw [guardC_of_stopped _ x.1 x.2 hstop];
     rcases x with ⟨sC, s_fig8, fl⟩; rfl)

theorem stepSimC_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ)
    (hstop : x.1.base.stopped = true) :
    stepSimC P ℓ Dh encPt encT decT idOf lam qep k q x = pure (smRangeNone q, x) := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact stepSimCNone_of_stopped P ℓ Dh encPt encT decT idOf lam qep _ x hstop
  · exact stepSimCNone_of_stopped P ℓ Dh encPt encT decT idOf lam qep _ x hstop
  · have hns : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim = false := by
      unfold simRecvStops JointC.sim; simp [hstop]
    simp only [stepSimC, hns, Bool.false_eq_true, ↓reduceIte]
    exact stepSimCNone_of_stopped P ℓ Dh encPt encT decT idOf lam qep _ x hstop
  · have hns : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim = false := by
      unfold simRecvStops JointC.sim; simp [hstop]
    simp only [stepSimC, hns, Bool.false_eq_true, ↓reduceIte]
    exact stepSimCNone_of_stopped P ℓ Dh encPt encT decT idOf lam qep _ x hstop
  · exact stepSimCNone_of_stopped P ℓ Dh encPt encT decT idOf lam qep _ x hstop

theorem stepSimCEager_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true)
    (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q x ec =
      pure (smRangeNone q, (x, ec)) := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r x ec = _
    unfold stepSimCEagerTransmit
    have hsim := stepSimEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inl (.inl (Q, m₀, r))))) x.sim ec hstop hec
    change stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r x.sim ec =
      pure (none, (x.sim, ec)) at hsim
    rw [hsim]
    rcases x with ⟨sC, s_fig8, fl⟩
    rfl
  · change stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r x ec = _
    unfold stepSimCEagerChall
    have hsim := stepSimEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) x.sim ec hstop hec
    change stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r x.sim ec =
      pure (none, (x.sim, ec)) at hsim
    rw [hsim]
    rcases x with ⟨sC, s_fig8, fl⟩
    rfl
  · change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
    unfold stepSimCEagerDeliver
    have huse : simRecvUsesCoin P encT decT k Q w true x.sim = false := by
      unfold simRecvUsesCoin JointC.sim; simp [hstop]
    simp only [huse, evictStopsC_of_stopped P encT decT k Q w true x hstop, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte]
    rw [stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop,
      pure_bind, updateAllEagerCoins_self_unused x.1.base.mir ec hec, pure_bind]
  · change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
    unfold stepSimCEagerInject
    have huse : simRecvUsesCoin P encT decT k Q w false x.sim = false := by
      unfold simRecvUsesCoin JointC.sim; simp [hstop]
    simp only [huse, evictStopsC_of_stopped P encT decT k Q w false x hstop, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte]
    rw [stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop,
      pure_bind, updateAllEagerCoins_self_unused x.1.base.mir ec hec, pure_bind]
  · change stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q x ec = _
    unfold stepSimCEagerCorr
    rw [stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop,
      pure_bind, updateAllEagerCoins_self_unused x.1.base.mir ec hec, pure_bind]

/-- Once `x.1.base.stopped = true` under `ValidEagerCoins`, running any continuation under `runSimCEager` preserves `stopped = true` and `s_fig8.win`. -/
theorem evalDist_runSimCEager_stopped_and_win {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true)
    (hec : ValidEagerCoins x.1.base.mir ec) :
    𝒟[runSimCEager P ℓ Dh encPt encT decT idOf lam qep k oa x ec >>=
        fun r => pure (r.2.1.1.base.stopped && r.2.1.2.1.win)] =
      𝒟[(pure x.2.1.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp [runSimCEager_pure, hstop]
  | query_bind q' cont ih =>
    rcases q' with u | q
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inl_bind, bind_assoc]
      refine (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool))
        fun y => ih y).trans ?_
      exact OracleComp.evalDist_bind_const _ _
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inr_bind,
        stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k q x ec hstop hec,
        pure_bind]
      exact ih (smRangeNone q)

theorem stepSimCEager_inject_eq_eager (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec =
      (let res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec
       let used : Party → Bool :=
         if simRecvUsesCoin P encT decT k Q w false x.sim then (· == Q) else (fun _ => false)
       updateAllEagerCoins x.1.base.mir res.2.1.mir used ec >>= fun ec' =>
         pure (res.1, (x.withSim res.2, ec'))) := by
  change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
  unfold stepSimCEagerInject simRecvStepEager
  unfold simRecvStepEager at hstop
  simp only [hnpW, Bool.not_false, Bool.and_true]
  by_cases huse : simRecvUsesCoin P encT decT k Q w false x.sim = true
  · simp [huse]
  · simp only [Bool.not_eq_true] at huse
    simp only [huse, Bool.false_eq_true, ↓reduceIte] at hstop ⊢
    rw [evictStopsC_of_simRecvStep_stopped P ℓ Dh encPt encT decT idOf lam qep k k Q w false 0 x hstop]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hstepC : stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x =
        pure ((simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 x.sim).1,
          x.withSim (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 x.sim).2) := by
      by_cases hs0 : x.1.base.stopped = true
      · rw [stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hs0]
        have hsr : simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 x.sim = (none, x.sim) := by
          unfold simRecvStep JointC.sim; simp [hs0]
        rw [hsr]
        rcases x with ⟨sC, s_fig8, fl⟩
        rfl
      · simp only [Bool.not_eq_true] at hs0
        have hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim = true := by
          rw [simRecvStops_eq_of_not_recvPanicsW P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim
            hnpW hs0, hstop]
        simp only [stepSimC, hstops, ↓reduceIte]
        rw [stepSim_inject_eq]
        simp [huse]
    rw [hstepC, pure_bind]
    rfl

/-- When `simRecvStepEager` on an inject query sets `stopped = true`, running the continuation yields `stopped && win` distributed as `pure res.2.2.win`. -/
theorem evalDist_stepSimCEager_inject_stopped {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false) :
    𝒟[stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win)] =
      𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec).2.2.win : ProbComp Bool)] := by
  set res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec
  rw [stepSimCEager_inject_eq_eager P ℓ Dh encPt encT decT idOf lam qep k Q w x ec hstop hnpW]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ (pure res.2.2.win) ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir res.2.1.mir _ ec ec' hec'
  exact evalDist_runSimCEager_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep k
    (cont res.1) (x.withSim res.2) ec' hstop hvalid

/-- Decomposes `runWinAtC` across an ambiguous `inject` query that increments `amb` at `k = none` and stops at `k = some x.1.base.amb`. -/
theorem evalDist_runWinAtC_inr_inject_amb {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w false x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inr (Q, w))) x ec =
      pure (some SM.RecvResult.rejected, (({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2.1, x.2.2), ec)))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w false x.sim ec).2.2.win
    let winBefore' := fun j =>
      if j = x.1.base.amb then w0
      else winBefore j
    𝒟[runWinAtC P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
          (.inr (.inl (.inr (Q, w))))) >>= cont)
        x ec winBefore idx] =
      𝒟[runWinAtC P ℓ Dh encPt encT decT idOf lam qep (cont (some SM.RecvResult.rejected))
        ({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2.1, x.2.2) ec winBefore' idx] := by
  intro w0 winBefore'
  unfold runWinAtC
  cases idx with
  | zero =>
    rw [runSimCEager_inr_bind, hnone, pure_bind]
  | succ j =>
    dsimp only
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp [hlt, hlt', winBefore', hne0]
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0
        have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore', runSimCEager_inr_bind, bind_assoc]
        exact evalDist_stepSimCEager_inject_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some x.1.base.amb) Q w cont x ec hstop0 hnpW
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEager_inr_bind]
        rw [stepSimCEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inr (Q, w))) x ec heq0,
            hnone, pure_bind]

/-! ## Ambiguous-inject rejection -/

theorem simInvC_inject_amb_reject
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ) (hr : 0 < r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {w0 : Bool} (hw0 : w0 = false) :
    let winBefore' := fun j =>
      if j = s.amb then w0
      else winBefore j
    SimInvC P Inv ℓ Dh encPt encT qep q (r - 1) x₀
      s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore' epExp := by
  intro winBefore'
  have hamb := hinv.hamb
  refine
    { hmeta := ⟨hinv.hmeta.hb, hinv.hmeta.hwin_R, hinv.hmeta.hwin_mir, hinv.hmeta.hwin_fig8,
        hinv.hmeta.hstop, hinv.hmeta.hepoch_R, hinv.hmeta.hepoch_fig8, hinv.hmeta.hidx_R,
        hinv.hmeta.hidx_fig8, hinv.hmeta.htL_R, hinv.hmeta.htL_fig8, hinv.hmeta.hchall_R,
        hinv.hmeta.hchall_fig8, hinv.hmeta.hcomp_R, hinv.hmeta.hcomp_fig8, hinv.hmeta.hcorrs_R,
        hinv.hmeta.hcorrs_fig8, hinv.hmeta.hmaxAcc_R, hinv.hmeta.hmaxAcc_fig8,
        hinv.hmeta.htrans_R, hinv.hmeta.htrans_fig8⟩
      hcomp := hinv.hcomp
      hec := hinv.hec
      hwinBefore := ?_
      hamb := by dsimp only; omega
      hamb_strict := fun hpos => by
        have hlt := hinv.hamb_strict hpos
        dsimp only; omega
      hidx_le := fun R => by
        have hle := hinv.hidx_le R
        dsimp only; omega
      hhon_len := by
        have hle := hinv.hhon_len
        dsimp only; omega
      hep_le := hinv.hep_le
      hep_adj := hinv.hep_adj
      hst_R := hinv.hst_R
      hst_id := hinv.hst_id
      htcur := hinv.htcur
      hepExp0 := hinv.hepExp0
      hspur := hinv.hspur
      hchainsA := hinv.hchainsA
      hchainsA_ep := hinv.hchainsA_ep
      hchainsB_ep := hinv.hchainsB_ep
      hchainsB_none := hinv.hchainsB_none
      hcorrB0 := hinv.hcorrB0
      hchains_sync := hinv.hchains_sync
      hhon := hinv.hhon
      htrans_hon := hinv.htrans_hon
      hcoll := hinv.hcoll
      hpqInv := hinv.hpqInv }
  intro j hj
  dsimp only [winBefore'] at hj ⊢
  by_cases h0 : j = s.amb
  · simp [h0, hw0]
  · simp only [h0, ↓reduceIte]
    exact hinv.hwinBefore j (by omega)

theorem simInvCX_inject_amb_reject
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {w0 : Bool} (hw0 : w0 = false) :
    let winBefore' := fun j =>
      if j = sC.base.amb then w0
      else winBefore j
    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
      s_R { sC with base := { sC.base with amb := sC.base.amb + 1 } } s_fig8 ec winBefore' epExp := by
  intro winBefore'
  have hsim' := (simInvC_inject_amb_reject P (InvB Inv q r) ℓ Dh encPt encT qep q r hr x₀
    s_R sC.base s_fig8 ec winBefore epExp hinv.hsim hw0).mono
    (fun Q => (hinv.hsim.hpqInv Q).mono (Nat.sub_le r 1))
  exact ⟨hsim', hinv.huniq, ⟨hinv.hkept.hfull, hinv.hkept.hrs, hinv.hkept.hvR⟩, hinv.hidx,
    hinv.hsync⟩

/-- Closes an ambiguous injection when `libsignalToModularSchemeSim` rejects at `k = none` with `amb + 1` and stops at `k = some sC.base.amb`, while libsignal rejects whenever the stopping win event is `false`. -/
theorem closeByStateC_inject_amb_reject {α : Type}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (post : α → Bool)
    (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !sC.base.mir.safeInj 3 ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w false (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w))) (sC, s_fig8, false) ec =
      pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)))
    (ih : ∀ s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore' epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
        (cont (some .rejected)) s_R' sC' s_fig8' fl' ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  cases hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w false (sC.base, s_fig8) ec).2.2.win with
  | true =>
    unfold CloseByStateC
    refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1)
      (Finset.mem_range.mpr (by have := hinv.hsim.hamb; omega)) ?_
    unfold runWinAtC
    have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
    simp only [hnlt, ↓reduceIte, runSimCEager_inr_bind, bind_assoc]
    rw [evalDist_stepSimCEager_inject_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some sC.base.amb) Q w cont (sC, s_fig8, false) ec hstop0 hnpW]
    change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w false
      (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
    rw [hw0]
    simp
  | false =>
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hsim.hmeta.hwin_R, hinv.hsim.hmeta.inTransit_R_isSome, hinv.hsim.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inr (Q, w))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_inject_eq]
      simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext rc
      unfold injectRPure
      simp [hguard_R, hrcv rc]
    have hguard_D0 : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false :=
      hguard_R
    have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inr (Q, w))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_inject_eq]
      simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext rc
      unfold injectRPure
      simp [hguard_D0, hrcv rc]
    let winBefore' := fun j =>
      if j = sC.base.amb then false
      else winBefore j
    have hinv' := simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀ s_R sC s_fig8 ec winBefore epExp hinv rfl
    have hih := ih s_R { sC with base := { sC.base with amb := sC.base.amb + 1 } } s_fig8 false ec winBefore' epExp hinv'
    unfold CloseByStateC at hih ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_ hih
    · rw [runRCont_inr_bind, hstepR]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · rw [runSimCEager_inr_bind, hnone]
      simp only [pure_bind]
    · intro idx _
      have h := evalDist_runWinAtC_inr_inject_amb P ℓ Dh encPt encT decT idOf lam qep Q w cont
        (sC, s_fig8, false) ec hstop0 hnpW hnone winBefore idx
      dsimp only [JointC.sim] at h
      rw [hw0] at h
      exact h
    · rw [runRCont_inr_bind, hstepD0]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · unfold runHidC
      rw [runSimCEager_inr_bind, hnone, pure_bind]

theorem simRecvStepEager_inject_ambC
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false)
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true) :
    (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w false (s, s_fig8) ec).2.1.stopped = true ∧
    (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w false (s, s_fig8) ec).2.2.win =
      if inReceiveOnlyEpoch s.mir Q then spurPtStep P Dh encPt decT Q w false (ec Q) (s, s_fig8) else false := by
  have hdiv : ((some s.amb : Option ℕ) == some s.amb) = true := beq_self_eq_true _
  have huse : simRecvUsesCoin P encT decT (some s.amb) Q w false (s, s_fig8) = inReceiveOnlyEpoch s.mir Q := by
    unfold simRecvUsesCoin
    simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero, hamb_b, hdiv, hinv.hmeta.hwin_fig8]
    cases inReceiveOnlyEpoch s.mir Q <;> rfl
  unfold simRecvStepEager
  rw [huse]
  unfold simRecvStep
  simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
    Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
    hevict, hzero, hamb_b, hdiv, huse]
  cases inReceiveOnlyEpoch s.mir Q <;> simp

theorem hspk_corr_of_simInvC (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {g₀ : GhostChain} (hg₀ : g₀ ∈ s.chains .A) (hnone : g₀.key.isNone = true) :
    (.B, 0) ∉ s.mir.corrs := by
  intro hcorr
  have hf := hinv.hcorrB0 hcorr g₀ hg₀
  rw [hnone] at hf
  exact Bool.noConfusion hf

end CryptoGames.LibsignalSM.Proofs.Refinement
