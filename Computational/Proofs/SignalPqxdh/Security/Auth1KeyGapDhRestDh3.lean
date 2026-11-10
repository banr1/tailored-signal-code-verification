/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC4
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Pre-sampling and dead-flag preservation for one-key `Auth` Case C (`DH3`)

**Checked by Lean.** Defines the unlatched one-key `.g3` simulation `runAuthFgSim1Key` and the
Case C pre-sampled oracle `pqxdhAuthFgPreImpl1KeyDh3`, proving unlatch equivalence, scalar
pre-sampling equivalence, and preservation of `deadAuthDh3`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

theorem mem_support_pqxdhAuthImpl1Key_initPrin {S : Setup} (P : Primitives) (u : Fin S.N_id)
    (st : AuthState S) (x : AuthResponse × AuthState S)
    (hx : x ∈ support ((pqxdhAuthImpl1Key S P (.initPrin u)).run st)) :
    x.2 = st ∨
    (st.principals.any (fun (idx, _) => idx == u.val) = false ∧
      ∃ sk : Bytes, sk.length = 32 ∧
        x = (.initPrinResp (P.x25519Base sk) (P.x25519Base sk),
          { st with principals := (u.val,
            { secIKA0 := sk, ikAPk := P.x25519Base sk, secIKAsign := sk,
              ikSignPk := P.x25519Base sk, corrupted := false }) :: st.principals })) := by
  unfold pqxdhAuthImpl1Key at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  revert hx
  cases hAny : st.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    rintro ⟨sk, hsk, hEq⟩
    exact Or.inr ⟨trivial, sk, length_of_mem_support_sampleScalar32 hsk, hEq⟩
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hEq; exact Or.inl (by rw [hEq])

/-- Unlatched one-key reference `.g3` `Auth` simulation (`pqxdhAuthFgImpl1Key`). -/
noncomputable def runAuthFgSim1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp (Bool × Bool × AuthFgCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthFgCutoffState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgImpl1Key S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

theorem map_unlatchFg_pqxdhAuthFgLatchedImpl1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S) :
    Prod.map id unlatchFg <$> ((pqxdhAuthFgLatchedImpl1Key S P q).run hst) =
      (pqxdhAuthFgImpl1Key S P q).run (unlatchFg hst) := by
  cases q with
  | initPrin u =>
    simp [pqxdhAuthFgLatchedImpl1Key, pqxdhAuthFgImpl1Key, liftAuthFgBase, unlatchFg,
      StateT.run_mk, Prod.map]
  | _ => exact map_unlatchFg_pqxdhAuthFgLatchedImpl S P _ hst

theorem map_unlatchFg_fullAuthFgLatchedImpl1Key (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthFgCutoffState S) :
    Prod.map id unlatchFg <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthFgCutoffState S) ProbComp) +
        pqxdhAuthFgLatchedImpl1Key S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgImpl1Key S P) q).run (unlatchFg hst) := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr gq => exact map_unlatchFg_pqxdhAuthFgLatchedImpl1Key S P gq hst

theorem runAuthFgLatchedSim1Key_bind_of_unlatch_inv (S : Setup) (P : Primitives)
    (A : AuthAdversary S) {β : Type}
    (obs : Bool × Bool × AuthFgCutoffState S → ProbComp β)
    (hInv : ∀ secb b' hst, obs (secb, b', unlatchFg hst) = obs (secb, b', hst)) :
    (runAuthFgLatchedSim1Key S P A >>= obs) = (runAuthFgSim1Key S P A >>= obs) := by
  unfold runAuthFgLatchedSim1Key runAuthFgSim1Key
  simp only [bind_assoc, pure_bind]
  congr 1; funext secb
  have hSim := congrArg (· >>= fun p => obs (secb, p.1, p.2))
    (_root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
      unlatchFg
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgLatchedImpl1Key S P)
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgImpl1Key S P)
      (map_unlatchFg_fullAuthFgLatchedImpl1Key S P)
      A.run (AuthFgCutoffState.empty S secb))
  dsimp only [unlatchFg_empty] at hSim
  rw [← hSim, map_eq_bind_pure_comp]
  simp [bind_assoc, Prod.map, hInv]

theorem evalDist_runAuthFgLatchedSim1Key_badAuthFgDh3At_eq (S : Setup) (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (A : AuthAdversary S) :
    (runAuthFgLatchedSim1Key S P A >>= fun x =>
      pure (badAuthFgDh3At P maxLen sIdx bIdx x.2.2.base x.2.2.advRoLog x.2.2.respRecs)) =
    (runAuthFgSim1Key S P A >>= fun x =>
      pure (badAuthFgDh3At P maxLen sIdx bIdx x.2.2.base x.2.2.advRoLog x.2.2.respRecs)) :=
  runAuthFgLatchedSim1Key_bind_of_unlatch_inv S P A _ (fun _ _ _ => rfl)

/-- Pre-sampled one-key `.g3` `Auth` oracle for Case C (`DH3`). -/
noncomputable def pqxdhAuthFgPreImpl1KeyDh3 (targetIdx targetSpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .initPrin u => liftAuthFgBase (pqxdhAuthImpl1Key S P (.initPrin u))
  | q => pqxdhAuthFgPreImpl false targetIdx targetSpkIdx optUsk optVsk S P q

theorem pqxdhAuthFgPreImpl1KeyDh3_of_not_initPrin {S : Setup} (targetIdx targetSpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (P : Primitives) (q : AuthQuery S)
    (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx optUsk optVsk S P q =
      pqxdhAuthFgPreImpl false targetIdx targetSpkIdx optUsk optVsk S P q := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

theorem pqxdhAuthFgPreImpl1KeyDh3_none_none_eq {S : Setup} (targetIdx targetSpkIdx : ℕ)
    (P : Primitives) :
    pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx none none S P = pqxdhAuthFgImpl1Key S P := by
  funext q
  cases q
  case initPrin u => rfl
  all_goals
    simpa [pqxdhAuthFgPreImpl1KeyDh3, pqxdhAuthFgImpl1Key] using
      congrFun (pqxdhAuthFgPreImpl_none_none_eq (S := S) false targetIdx targetSpkIdx P) _

theorem liftAuthFgBase_initPrin1Key_preserves_hasFired {S : Setup} (P : Primitives)
    (u : Fin S.N_id) (hst : AuthFgCutoffState S) (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support ((liftAuthFgBase (pqxdhAuthImpl1Key S P (.initPrin u))).run hst)) :
    (∀ bIdx, hasFiredAuthSpk S bIdx hst → hasFiredAuthSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredAuthPrin S uIdx hst → hasFiredAuthPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredAuthSess S sIdx hst → hasFiredAuthSess S sIdx x.2) := by
  rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
  rcases mem_support_pqxdhAuthImpl1Key_initPrin P u hst.base _ hb with hB | ⟨_, sk, _, hEq⟩
  · try dsimp only at hB
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hB]; exact h,
      fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hB]; exact h⟩
  · have hB := (Prod.mk.inj hEq).2
    try dsimp only at hB
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hB]; simp [h],
      fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hB]; exact h⟩

theorem pqxdhAuthFgPreImpl1KeyDh3_preserves_hasFired {S : Setup}
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx optUsk optVsk S P q).run hst)) :
    (∀ bIdx, hasFiredAuthSpk S bIdx hst → hasFiredAuthSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredAuthPrin S uIdx hst → hasFiredAuthPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredAuthSess S sIdx hst → hasFiredAuthSess S sIdx x.2) := by
  cases q
  case initPrin u => exact liftAuthFgBase_initPrin1Key_preserves_hasFired P u hst x hx
  all_goals
    exact pqxdhAuthFgPreImpl_preserves_hasFired false targetIdx targetSpkIdx optUsk optVsk
      P _ hst x hx

theorem evalDist_preSample_V_pqxdhAuthFgPreImpl1KeyDh3 {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredAuthSpk S targetSpkIdx)
    (pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx optUsk none S P)
    (fun vSk => pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgPreImpl1KeyDh3_preserves_hasFired targetIdx targetSpkIdx optUsk none P q s x
        hx).1 targetSpkIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | genSPK u j =>
      unfold pqxdhAuthFgPreImpl1KeyDh3 pqxdhAuthFgPreImpl
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
      unfold pqxdhAuthFgPreImpl1KeyDh3 pqxdhAuthFgPreImpl
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
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc, MonadAttach.mem_support_bind,
                support_pure, Set.mem_singleton_iff] at hx
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

theorem evalDist_preSample_U_dh3_pqxdhAuthFgPreImpl1KeyDh3 {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq_c0
    sampleScalar32
    sampleAuthSendCoins
    (hasFiredAuthSess S targetIdx)
    (pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhAuthFgPreImpl1KeyDh3 targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgPreImpl1KeyDh3_preserves_hasFired targetIdx targetSpkIdx
        none optVsk P q s x hx).2.2
        targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl1KeyDh3 pqxdhAuthFgPreImpl liftAuthFgHybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isNone
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [fgPreAuthSendHybrid_eq_of_hasFiredAuthSess targetIdx uSk P (.sendOPK u i)
          (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
          u bundle m0 m1 s hFired]
      · rfl
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl1KeyDh3 pqxdhAuthFgPreImpl liftAuthFgHybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [fgPreAuthSendHybrid_eq_of_hasFiredAuthSess targetIdx uSk P (.sendNoOPK u i)
          (initSessionSlotIdx_sendNoOPK_lt u i) u bundle m0 m1 s hFired]
      · rfl
    | _ => rfl
  · cases q with
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl1KeyDh3 pqxdhAuthFgPreImpl
      by_cases hOpt : bundle.opkB?.isNone = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftAuthFgHybrid; simp [hOpt]
      · have hEqPre : ∀ optU, (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isNone then return .noneResp
            fgPreAuthSendHybrid .g3 true false targetIdx optU S P
              (.sendOPK u i) u bundle m0 m1)).run s =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false targetIdx optU S P
            (.sendOPK u i) u bundle m0 m1)).run s := by
          intro optU; unfold liftAuthFgHybrid; simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreAuthSend_before_c0 targetIdx P hP (.sendOPK u i) u bundle m0 m1 s
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl1KeyDh3 pqxdhAuthFgPreImpl
      by_cases hOpt : bundle.opkB?.isSome = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftAuthFgHybrid; simp [hOpt]
      · have hEqPre : ∀ optU, (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isSome then return .noneResp
            fgPreAuthSendHybrid .g3 true false targetIdx optU S P
              (.sendNoOPK u i) u bundle m0 m1)).run s =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false targetIdx optU S P
            (.sendNoOPK u i) u bundle m0 m1)).run s := by
          intro optU; unfold liftAuthFgHybrid; simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreAuthSend_before_c0 targetIdx P hP (.sendNoOPK u i) u bundle m0 m1 s
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_runAuthFgSim1Key_eq_preSample_dh3 {S : Setup}
    (sIdx bIdx : ℕ) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S)
    (obs : Bool × Bool × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := AuthFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runAuthFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runAuthFgSim1Key
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
        pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx (some uSk) none S P) A.run).run
          (AuthFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx (some uSk) P A.run
      (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh3_pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx none P hP A.run
    (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhAuthFgPreImpl1KeyDh3_none_none_eq]
  simp only [pure_bind]

theorem pqxdhAuthFgPreImpl1KeyDh3_preserves_deadAuthDh3 {S : Setup} (P : Primitives)
    (sIdx bIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) x.2 = true := by
  cases q
  case initPrin u =>
    intro x hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    rcases mem_support_pqxdhAuthImpl1Key_initPrin P u hst.base _ hb with hB | ⟨_, sk, _, hEq⟩
    · try dsimp only at hB
      rw [AuthDh3.deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ (hst1 := hst) (hst2 := x.2)
        (by rw [hB]) (by rw [hB]) (by rw [hB])]
      exact hDead
    · have hB := (Prod.mk.inj hEq).2
      try dsimp only at hB
      rw [AuthDh3.deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ (hst1 := hst) (hst2 := x.2)
        (by rw [hB]) (by rw [hB]) (by rw [hB])]
      exact hDead
  all_goals
    exact pqxdhAuthFgPreImpl_preserves_deadAuthDh3 P sIdx bIdx hsIdx uSk vSk _ hst hDead

end Proofs.SignalPqxdh.Security
