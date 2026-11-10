/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# `Auth` hop `G3 → G3.5`: sticky-latch `DH1` simulation and monotonicity

Introduces the `.corruptIK`-latched `.g3` simulation `runAuthFgLatchedSim`, proves its
target-pre-sampling equivalence for `DH1`, and shows `.corruptIK` monotonicity on `AuthAdvLatchedState`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-! ## `latchDh1ForPrincipal` properties -/

theorem badAuthFgDh1At_imp_length {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (h : badAuthFgDh1At P maxLen uIdx bIdx st advRoLog respRecs = true) :
    badAuthFgDh1At P advRoLog.length uIdx bIdx st advRoLog respRecs = true := by
  unfold badAuthFgDh1At at h ⊢
  revert h
  cases st.principals.find? (fun (u, _) => u == uIdx) with
  | none => intro h; cases h
  | some up =>
    rcases up with ⟨_, uEntry⟩
    cases st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => intro h; cases h
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      dsimp only
      rw [List.take_length]
      intro h
      rcases Bool.and_eq_true_iff.mp h with ⟨hNotCorr, hOr⟩
      refine Bool.and_eq_true_iff.mpr ⟨hNotCorr, ?_⟩
      rcases Bool.or_eq_true_iff.mp hOr with hOr12 | hOr3
      · rcases Bool.or_eq_true_iff.mp hOr12 with hOr1 | hOr2
        · rcases List.any_eq_true.mp hOr1 with ⟨sec, hSecTake, hSecEq⟩
          have hSecMem : sec ∈ advRoLog := List.mem_of_mem_take hSecTake
          exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr
            (Or.inl (List.any_eq_true.mpr ⟨sec, hSecMem, hSecEq⟩))))
        · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr hOr2)))
      · exact Bool.or_eq_true_iff.mpr (Or.inr hOr3)

theorem contains_latchDh1ForPrincipal_of_contains {S : Setup} (P : Primitives) (uVal : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (latched : List (Nat × Nat)) {p : Nat × Nat}
    (h : latched.contains p = true) :
    (latchDh1ForPrincipal S P uVal st advRoLog respRecs latched).contains p = true := by
  unfold latchDh1ForPrincipal
  rw [List.contains_iff_mem] at h ⊢
  exact List.mem_append_right _ h

theorem contains_latchDh1ForPrincipal_of_badAuthFgDh1At {S : Setup} (P : Primitives)
    (maxLen uVal bIdx : ℕ) (hb : bIdx < S.N_spk_tot)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (latched : List (Nat × Nat))
    (hBad : badAuthFgDh1At P maxLen uVal bIdx st advRoLog respRecs = true) :
    (latchDh1ForPrincipal S P uVal st advRoLog respRecs latched).contains (uVal, bIdx) = true := by
  have hBadLen := badAuthFgDh1At_imp_length P maxLen uVal bIdx st advRoLog respRecs hBad
  unfold latchDh1ForPrincipal
  rw [List.contains_iff_mem]
  refine List.mem_append_left _ ?_
  refine List.mem_map.mpr ⟨bIdx, ?_, rfl⟩
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hb, hBadLen⟩

theorem mem_latchDh1ForPrincipal_iff {S : Setup} (P : Primitives) (uVal : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (latched : List (Nat × Nat)) (uIdx bIdx : ℕ) :
    (uIdx, bIdx) ∈ latchDh1ForPrincipal S P uVal st advRoLog respRecs latched ↔
      (uIdx = uVal ∧ bIdx < S.N_spk_tot ∧
        badAuthFgDh1At P advRoLog.length uVal bIdx st advRoLog respRecs = true) ∨
      (uIdx, bIdx) ∈ latched := by
  unfold latchDh1ForPrincipal
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨b', hb', hEq⟩ | hMem)
    · injection hEq with hu hb
      subst hu; subst hb
      rcases List.mem_filter.mp hb' with ⟨hRange, hBad⟩
      exact Or.inl ⟨rfl, List.mem_range.mp hRange, hBad⟩
    · exact Or.inr hMem
  · rintro (⟨rfl, hbLt, hBad⟩ | hMem)
    · refine Or.inl ⟨bIdx, List.mem_filter.mpr ⟨List.mem_range.mpr hbLt, hBad⟩, rfl⟩
    · exact Or.inr hMem

theorem contains_latchDh1ForPrincipal_of_ne {S : Setup} (P : Primitives)
    {uVal uIdx : ℕ} (hNe : uIdx ≠ uVal) (bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (latched : List (Nat × Nat)) :
    (latchDh1ForPrincipal S P uVal st advRoLog respRecs latched).contains (uIdx, bIdx) =
      latched.contains (uIdx, bIdx) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem, mem_latchDh1ForPrincipal_iff]
  constructor
  · rintro (⟨hEq, _, _⟩ | hMem)
    · exact False.elim (hNe hEq)
    · exact hMem
  · intro hMem; exact Or.inr hMem

/-! ## Latched `.g3` simulation -/

def unlatchFg {S : Setup} (hst : AuthFgCutoffState S) : AuthFgCutoffState S :=
  { hst with latchedDh1 := [] }

@[simp]
theorem unlatchFg_empty (S : Setup) (secb : Bool) :
    unlatchFg (AuthFgCutoffState.empty S secb) = AuthFgCutoffState.empty S secb := rfl

@[simp]
theorem unlatchFg_base {S : Setup} (hst : AuthFgCutoffState S) :
    (unlatchFg hst).base = hst.base := rfl

@[simp]
theorem unlatchFg_advRoLog {S : Setup} (hst : AuthFgCutoffState S) :
    (unlatchFg hst).advRoLog = hst.advRoLog := rfl

@[simp]
theorem unlatchFg_respRecs {S : Setup} (hst : AuthFgCutoffState S) :
    (unlatchFg hst).respRecs = hst.respRecs := rfl

/-- `.g3` `Auth` oracle on `AuthFgCutoffState S` that latches `badAuthFgDh1At` pairs right before `.corruptIK`. -/
def pqxdhAuthFgLatchedImpl (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .corruptIK u => StateT.mk (fun hst => do
    let latched' :=
      latchDh1ForPrincipal S P u.val hst.base hst.advRoLog hst.respRecs hst.latchedDh1
    let (resp, h') ←
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.corruptIK u)).run (mkG3Hybrid hst.base)
    return (resp, { hst with base := h'.base, latchedDh1 := latched' }))
  | q => pqxdhAuthFgImpl S P q

noncomputable def runAuthFgLatchedSim (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp (Bool × Bool × AuthFgCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthFgCutoffState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgLatchedImpl S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

theorem map_unlatchFg_pqxdhAuthFgLatchedImpl (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S) :
    Prod.map id unlatchFg <$> ((pqxdhAuthFgLatchedImpl S P q).run hst) =
      (pqxdhAuthFgImpl S P q).run (unlatchFg hst) := by
  cases q <;> simp [pqxdhAuthFgLatchedImpl, pqxdhAuthFgImpl, unlatchFg, StateT.run_mk, Prod.map]

theorem map_unlatchFg_fullAuthFgLatchedImpl (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthFgCutoffState S) :
    Prod.map id unlatchFg <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthFgCutoffState S) ProbComp) +
        pqxdhAuthFgLatchedImpl S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgImpl S P) q).run (unlatchFg hst) := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr gq => exact map_unlatchFg_pqxdhAuthFgLatchedImpl S P gq hst

theorem simulateQ_map_unlatchFg_fullAuthFgLatchedImpl (S : Setup) (P : Primitives)
    {α : Type} (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S) :
    let fullLatched := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgLatchedImpl S P
    let fullFg := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgImpl S P
    Prod.map id unlatchFg <$> ((simulateQ fullLatched oa).run hst) =
      (simulateQ fullFg oa).run (unlatchFg hst) :=
  _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    unlatchFg
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgLatchedImpl S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgImpl S P)
    (map_unlatchFg_fullAuthFgLatchedImpl S P)
    oa hst

/-- Observations independent of `latchedDh1` have identical distributions under `runAuthFgLatchedSim` and `runAuthFgSim`. -/
theorem runAuthFgLatchedSim_bind_of_unlatch_inv (S : Setup) (P : Primitives)
    (A : AuthAdversary S) {β : Type}
    (obs : Bool × Bool × AuthFgCutoffState S → ProbComp β)
    (hInv : ∀ secb b' hst, obs (secb, b', unlatchFg hst) = obs (secb, b', hst)) :
    (runAuthFgLatchedSim S P A >>= obs) = (runAuthFgSim S P A >>= obs) := by
  unfold runAuthFgLatchedSim runAuthFgSim
  simp only [bind_assoc, pure_bind]
  congr 1; funext secb
  have hSim := congrArg (· >>= fun p => obs (secb, p.1, p.2))
    (simulateQ_map_unlatchFg_fullAuthFgLatchedImpl S P A.run (AuthFgCutoffState.empty S secb))
  dsimp only [unlatchFg_empty] at hSim
  rw [← hSim, map_eq_bind_pure_comp]
  simp [bind_assoc, Prod.map, hInv]

theorem evalDist_runAuthFgLatchedSim_badAuthFgDh3At_eq (S : Setup) (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (A : AuthAdversary S) :
    (runAuthFgLatchedSim S P A >>= fun x =>
      pure (badAuthFgDh3At P maxLen sIdx bIdx x.2.2.base x.2.2.advRoLog x.2.2.respRecs)) =
    (runAuthFgSim S P A >>= fun x =>
      pure (badAuthFgDh3At P maxLen sIdx bIdx x.2.2.base x.2.2.advRoLog x.2.2.respRecs)) :=
  runAuthFgLatchedSim_bind_of_unlatch_inv S P A _ (fun _ _ _ => rfl)

/-! ## Pre-sampled latched `.g3` oracle -/

/-- Target-pre-sampled `.g3` `Auth` oracle with sticky `latchedDh1` updates on `.corruptIK`. -/
noncomputable def pqxdhAuthFgLatchedPreImpl (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .corruptIK u => pqxdhAuthFgLatchedImpl S P (.corruptIK u)
  | q => pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q

theorem pqxdhAuthFgLatchedPreImpl_none_none (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (P : Primitives) (q : AuthQuery S) :
    pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx none none S P q =
      pqxdhAuthFgLatchedImpl S P q := by
  have hPre := congrFun (pqxdhAuthFgPreImpl_none_none_eq useDh1 targetIdx targetSpkIdx P) q
  cases q with
  | corruptIK u => rfl
  | _ => exact hPre

theorem pqxdhAuthFgLatchedPreImpl_none_none_eq (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (P : Primitives) :
    pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx none none S P =
      pqxdhAuthFgLatchedImpl S P := by
  funext q
  exact pqxdhAuthFgLatchedPreImpl_none_none useDh1 targetIdx targetSpkIdx S P q

theorem exists_support_pqxdhAuthFgPreImpl_of_latched {S : Setup}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes)
    (P : Primitives) (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst)) :
    ∃ x' ∈ support
      ((pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst),
      x'.1 = x.1 ∧ x'.2.base = x.2.base ∧
      x'.2.advRoLog = x.2.advRoLog ∧ x'.2.respRecs = x.2.respRecs := by
  cases q with
  | corruptIK u =>
    unfold pqxdhAuthFgLatchedPreImpl pqxdhAuthFgLatchedImpl at hx
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, h'⟩, hh, rfl⟩
    refine ⟨(resp, { hst with base := h'.base }), ?_, rfl, rfl, rfl, rfl⟩
    unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    exact ⟨(resp, h'), hh, rfl⟩
  | _ =>
    exact ⟨x, hx, rfl, rfl, rfl, rfl⟩

theorem pqxdhAuthFgLatchedPreImpl_preserves_hasFired {S : Setup}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes)
    (P : Primitives) (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst)) :
    (∀ bIdx, hasFiredAuthSpk S bIdx hst → hasFiredAuthSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredAuthPrin S uIdx hst → hasFiredAuthPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredAuthSess S sIdx hst → hasFiredAuthSess S sIdx x.2) := by
  rcases exists_support_pqxdhAuthFgPreImpl_of_latched
    useDh1 targetIdx targetSpkIdx optUsk optVsk P q hst x hx with ⟨x', hx', _, hB, _, _⟩
  rcases pqxdhAuthFgPreImpl_preserves_hasFired
    useDh1 targetIdx targetSpkIdx optUsk optVsk P q hst x' hx' with ⟨h1, h2, h3⟩
  refine ⟨fun bIdx h => ?_, fun uIdx h => ?_, fun sIdx h => ?_⟩
  · have h' := h1 bIdx h
    rcases h' with ⟨u, j, hj, hMem⟩
    exact ⟨u, j, hj, hB ▸ hMem⟩
  · have h' := h2 uIdx h
    unfold hasFiredAuthPrin at h' ⊢
    rwa [← hB]
  · have h' := h3 sIdx h
    unfold hasFiredAuthSess at h' ⊢
    rwa [← hB]

theorem evalDist_preSample_V_pqxdhAuthFgLatchedPreImpl {S : Setup} {α : Type}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredAuthSpk S targetSpkIdx)
    (pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk none S P)
    (fun vSk => pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgLatchedPreImpl_preserves_hasFired
        useDh1 targetIdx targetSpkIdx optUsk none P q s x hx).1 targetSpkIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | genSPK u j =>
      unfold pqxdhAuthFgLatchedPreImpl pqxdhAuthFgPreImpl
      simp only [liftAuthFgHybrid_liftAuthBase_eq]
      unfold fgPreAuthGenSPK liftAuthFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hSlot : (spkBundleFlatIdx S u j == targetSpkIdx) = true
      · have hany := spkBundles_any_of_hasFiredAuthSpk S targetSpkIdx s hFired u j hSlot
        simp [hany]
      · cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => rfl
  · cases q with
    | genSPK u j =>
      unfold pqxdhAuthFgLatchedPreImpl pqxdhAuthFgPreImpl
      simp only [liftAuthFgHybrid_liftAuthBase_eq]
      by_cases hSlot : (spkBundleFlatIdx S u j == targetSpkIdx) = true
      · unfold fgPreAuthGenSPK liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => exact Or.inl (fun _ => rfl)
          | some p =>
            rcases p with ⟨_, uEntry⟩
            dsimp only
            refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure,
                StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure,
                StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind, bind_assoc,
                MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨rSpk, _, pqPair, _, rPq, _, hEq⟩
              have hB := (Prod.mk.inj hEq).2
              exact ⟨u, j, beq_iff_eq.mp hSlot, by rw [hB]; simp⟩
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        unfold fgPreAuthGenSPK liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_U_dh1_pqxdhAuthFgLatchedPreImpl {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl true targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl true targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredAuthPrin S targetIdx)
    (pqxdhAuthFgLatchedPreImpl true targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhAuthFgLatchedPreImpl true targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgLatchedPreImpl_preserves_hasFired
        true targetIdx targetSpkIdx none optVsk P q s x hx).2.1 targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | initPrin u =>
      unfold pqxdhAuthFgLatchedPreImpl pqxdhAuthFgPreImpl
      simp only [liftAuthFgHybrid_liftAuthBase_eq]
      unfold fgPreAuthInitPrin liftAuthFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
      by_cases hSlot : (u.val == targetIdx) = true
      · have heq : u.val = targetIdx := beq_iff_eq.mp hSlot
        unfold hasFiredAuthPrin at hFired
        rw [← heq] at hFired
        simp [hFired]
      · cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => rfl
  · cases q with
    | initPrin u =>
      unfold pqxdhAuthFgLatchedPreImpl pqxdhAuthFgPreImpl
      simp only [liftAuthFgHybrid_liftAuthBase_eq]
      by_cases hSlot : (u.val == targetIdx) = true
      · unfold fgPreAuthInitPrin liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun uSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure,
              StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure,
              StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind, bind_assoc,
              MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨secIKAsign, _, hEq⟩
            have hB := (Prod.mk.inj hEq).2
            unfold hasFiredAuthPrin
            rw [hB]
            simp [hSlot]
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun uSk => ?_)
        unfold fgPreAuthInitPrin liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_runAuthFgLatchedSim_eq_preSample_dh1 {S : Setup}
    (uIdx bIdx : ℕ) (P : Primitives) (A : AuthAdversary S)
    (obs : Bool × Bool × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl true uIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := AuthFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runAuthFgLatchedSim S P A >>= obs] := by
  intro fullPre
  unfold runAuthFgLatchedSim
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (AuthFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthFgCutoffState S) ProbComp) +
        pqxdhAuthFgLatchedPreImpl true uIdx bIdx (some uSk) none S P) A.run).run
          (AuthFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_pqxdhAuthFgLatchedPreImpl true uIdx bIdx (some uSk) P A.run
      (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh1_pqxdhAuthFgLatchedPreImpl uIdx bIdx none P A.run
    (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhAuthFgLatchedPreImpl_none_none_eq]
  simp only [pure_bind]

/-! ## `AuthAdvLatchedState` and `.corruptIK` monotonicity -/

/-- Pairs `AuthAdvCutoffState S` with ghost `latchedDh1` state for `.g3`/`.g3_5` coupling. -/
structure AuthAdvLatchedState (S : Setup) where
  adv        : AuthAdvCutoffState S
  latchedDh1 : List (Nat × Nat) := []

def AuthAdvLatchedState.empty (S : Setup) (secb : Bool) : AuthAdvLatchedState S :=
  { adv        := AuthAdvCutoffState.empty S secb
    latchedDh1 := [] }

def AuthAdvLatchedState.toFg {S : Setup} (s : AuthAdvLatchedState S) : AuthFgCutoffState S :=
  { base       := s.adv.hyb.base
    advRoLog   := s.adv.advRoLog
    respRecs   := s.adv.respRecs
    latchedDh1 := s.latchedDh1 }

def AuthAdvLatchedState.hyb {S : Setup} (s : AuthAdvLatchedState S) : AuthHybridState S :=
  s.adv.hyb

@[simp]
theorem AuthAdvLatchedState.toFg_empty (S : Setup) (secb : Bool) :
    (AuthAdvLatchedState.empty S secb).toFg = AuthFgCutoffState.empty S secb := rfl

@[simp]
theorem AuthAdvLatchedState.adv_empty (S : Setup) (secb : Bool) :
    (AuthAdvLatchedState.empty S secb).adv = AuthAdvCutoffState.empty S secb := rfl

@[simp]
theorem AuthAdvLatchedState.hyb_empty (S : Setup) (secb : Bool) :
    (AuthAdvLatchedState.empty S secb).hyb = AuthHybridState.empty S secb := rfl

def pqxdhAuthAdvLatchedStageImpl (stage : AuthHybridStage) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthAdvLatchedState S) ProbComp)
  | .corruptIK u => StateT.mk (fun s => do
    let latched' :=
      latchDh1ForPrincipal S P u.val s.adv.hyb.base s.adv.advRoLog s.adv.respRecs s.latchedDh1
    let (resp, adv') ← (pqxdhAuthAdvStageImpl stage S P (.corruptIK u)).run s.adv
    return (resp, { adv := adv', latchedDh1 := latched' }))
  | q => StateT.mk (fun s => do
    let (resp, adv') ← (pqxdhAuthAdvStageImpl stage S P q).run s.adv
    return (resp, { s with adv := adv' }))

theorem map_adv_pqxdhAuthAdvLatchedStageImpl (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S) :
    Prod.map id AuthAdvLatchedState.adv <$>
        ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s) =
      (pqxdhAuthAdvStageImpl stage S P q).run s.adv := by
  cases q <;> simp [pqxdhAuthAdvLatchedStageImpl, StateT.run_mk, Prod.map]

theorem map_adv_fullAuthAdvLatchedStageImpl (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) (q : (unifSpec + authSpec S).Domain) (s : AuthAdvLatchedState S) :
    Prod.map id AuthAdvLatchedState.adv <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthAdvLatchedState S) ProbComp) +
        pqxdhAuthAdvLatchedStageImpl stage S P) q).run s =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvCutoffState S) ProbComp) +
      pqxdhAuthAdvStageImpl stage S P) q).run s.adv := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr gq => exact map_adv_pqxdhAuthAdvLatchedStageImpl stage S P gq s

theorem simulateQ_map_adv_fullAuthAdvLatchedStageImpl (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) {α : Type} (oa : OracleComp (unifSpec + authSpec S) α)
    (s : AuthAdvLatchedState S) :
    let fullLatched := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvLatchedState S) ProbComp) + pqxdhAuthAdvLatchedStageImpl stage S P
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl stage S P
    Prod.map id AuthAdvLatchedState.adv <$> ((simulateQ fullLatched oa).run s) =
      (simulateQ fullAdv oa).run s.adv :=
  _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    AuthAdvLatchedState.adv
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthAdvLatchedState S) ProbComp) + pqxdhAuthAdvLatchedStageImpl stage S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl stage S P)
    (map_adv_fullAuthAdvLatchedStageImpl stage S P)
    oa s

theorem authKoskExpAtStage_eq_advLatchedStage (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage stage S P A =
    (do
      let secb ← $ᵗ Bool
      let initSt := AuthAdvLatchedState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthAdvLatchedState S) ProbComp) +
        pqxdhAuthAdvLatchedStageImpl stage S P
      let (b', finalSt) ← (simulateQ impl A.run).run initSt
      finalizeAuthKosk S P secb b' finalSt.hyb) := by
  rw [authKoskExpAtStage_eq_advStage stage S P A]
  congr 1; funext secb
  have hsim := congrArg
    (· >>= fun (p : Bool × AuthAdvCutoffState S) => finalizeAuthKosk S P secb p.1 p.2.hyb)
    (simulateQ_map_adv_fullAuthAdvLatchedStageImpl stage S P A.run
      (AuthAdvLatchedState.empty S secb))
  dsimp only [AuthAdvLatchedState.adv_empty] at hsim
  rw [← hsim, map_eq_bind_pure_comp]
  simp [bind_assoc, Prod.map, AuthAdvLatchedState.hyb]

theorem lookupSenderIkPk_map_corrupt (uVal sIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) :
    lookupSenderIkPk
      (principals.map (fun (idx, e) =>
        if idx == uVal then (idx, { e with corrupted := true }) else (idx, e)))
      sIdx = lookupSenderIkPk principals sIdx := by
  unfold lookupSenderIkPk
  induction principals with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    simp only [List.map_cons]
    cases h1 : (idx == uVal) <;> cases h2 : (idx == sIdx) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.find?_cons, h2]
    · exact ih
    · exact ih

end Proofs.SignalPqxdh.Security
