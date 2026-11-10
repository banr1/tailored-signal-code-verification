/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdPre
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3b
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Pre-sampled latched `.g3` oracle for one-key `Auth` Case A (`DH1`)

**Checked by Lean.** Defines the pre-sampled one-key latched `.g3` `Auth` oracle
`pqxdhAuthFgLatchedPreImpl1Key` and proves that pre-sampling the target identity scalar and SPK
scalar preserves the output distribution of `runAuthFgLatchedSim1Key`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

noncomputable def fgPreAuthInitPrin1Key (prinFlag : Bool) (prinIdx : ℕ) (optPrinSk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    StateT (AuthState S) ProbComp AuthResponse := do
  let st ← get
  if st.principals.any (fun (idx, _) => idx == u.val) then
    return .noneResp
  let secIKA0 ← liftM (match optPrinSk with
    | some s => if prinFlag && (u.val == prinIdx) then pure s else sampleScalar32
    | none => sampleScalar32)
  let ikAPk := P.x25519Base secIKA0
  let entry : PrincipalEntry := {
    secIKA0    := secIKA0
    ikAPk      := ikAPk
    secIKAsign := secIKA0
    ikSignPk   := ikAPk
    corrupted  := false
  }
  set { st with principals := (u.val, entry) :: st.principals }
  return .initPrinResp ikAPk ikAPk

theorem fgPreAuthInitPrin1Key_none_eq (prinFlag : Bool) (prinIdx : ℕ) (S : Setup)
    (P : Primitives) (u : Fin S.N_id) :
    fgPreAuthInitPrin1Key prinFlag prinIdx none S P u = pqxdhAuthImpl1Key S P (.initPrin u) := rfl

/-- One-key pre-sampled latched `.g3` `Auth` oracle. -/
noncomputable def pqxdhAuthFgLatchedPreImpl1Key (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .initPrin u => liftAuthFgBase (fgPreAuthInitPrin1Key useDh1 targetIdx optUsk S P u)
  | q => pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q

theorem pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : AuthQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk optVsk S P q =
      pqxdhAuthFgLatchedPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

theorem pqxdhAuthFgLatchedPreImpl1Key_none_none_eq {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (P : Primitives) :
    pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx targetSpkIdx none none S P =
      pqxdhAuthFgLatchedImpl1Key S P := by
  funext q
  cases q
  case initPrin u => rfl
  all_goals
    simpa [pqxdhAuthFgLatchedPreImpl1Key, pqxdhAuthFgLatchedImpl1Key] using
      pqxdhAuthFgLatchedPreImpl_none_none useDh1 targetIdx targetSpkIdx S P _

theorem fgPreAuthInitPrin1Key_preserves_hasFired {S : Setup} (prinFlag : Bool) (prinIdx : ℕ)
    (optPrinSk : Option Bytes) (P : Primitives) (u : Fin S.N_id) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support
      ((liftAuthFgBase (fgPreAuthInitPrin1Key prinFlag prinIdx optPrinSk S P u)).run hst)) :
    (∀ bIdx, hasFiredAuthSpk S bIdx hst → hasFiredAuthSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredAuthPrin S uIdx hst → hasFiredAuthPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredAuthSess S sIdx hst → hasFiredAuthSess S sIdx x.2) := by
  rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩; clear hx
  unfold fgPreAuthInitPrin1Key at hb
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
  revert hb
  cases hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    rintro ⟨sk, _, hEq⟩
    have hB := (Prod.mk.inj hEq).2
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hB]; simp [List.any_cons, h],
      fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hB]; exact h⟩
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hEq; have hB := (Prod.mk.inj hEq).2
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hB]; exact h,
      fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hB]; exact h⟩

theorem pqxdhAuthFgLatchedPreImpl1Key_preserves_hasFired {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst)) :
    (∀ bIdx, hasFiredAuthSpk S bIdx hst → hasFiredAuthSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredAuthPrin S uIdx hst → hasFiredAuthPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredAuthSess S sIdx hst → hasFiredAuthSess S sIdx x.2) := by
  cases q
  case initPrin u =>
    exact fgPreAuthInitPrin1Key_preserves_hasFired useDh1 targetIdx optUsk P u hst x hx
  all_goals
    exact pqxdhAuthFgLatchedPreImpl_preserves_hasFired useDh1 targetIdx targetSpkIdx optUsk optVsk
      P _ hst x hx

theorem evalDist_preSample_V_pqxdhAuthFgLatchedPreImpl1Key {S : Setup} {α : Type}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredAuthSpk S targetSpkIdx)
    (pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk none S P)
    (fun vSk => pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgLatchedPreImpl1Key_preserves_hasFired
        useDh1 targetIdx targetSpkIdx optUsk none P q s x hx).1 targetSpkIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | genSPK u j =>
      unfold pqxdhAuthFgLatchedPreImpl1Key pqxdhAuthFgLatchedPreImpl pqxdhAuthFgPreImpl
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
      unfold pqxdhAuthFgLatchedPreImpl1Key pqxdhAuthFgLatchedPreImpl pqxdhAuthFgPreImpl
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

theorem evalDist_preSample_U_dh1_pqxdhAuthFgLatchedPreImpl1Key {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl1Key true targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl1Key true targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredAuthPrin S targetIdx)
    (pqxdhAuthFgLatchedPreImpl1Key true targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhAuthFgLatchedPreImpl1Key true targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgLatchedPreImpl1Key_preserves_hasFired
        true targetIdx targetSpkIdx none optVsk P q s x hx).2.1 targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | initPrin u =>
      unfold pqxdhAuthFgLatchedPreImpl1Key fgPreAuthInitPrin1Key liftAuthFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
      by_cases hSlot : (u.val == targetIdx) = true
      · have hany : s.base.principals.any (fun (idx, _) => idx == u.val) = true := by
          unfold hasFiredAuthPrin at hFired
          rw [beq_iff_eq.mp hSlot]; exact hFired
        simp [hany]
      · cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => rfl
  · cases q with
    | initPrin u =>
      by_cases hSlot : (u.val == targetIdx) = true
      · unfold pqxdhAuthFgLatchedPreImpl1Key fgPreAuthInitPrin1Key liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun uSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind,
              support_pure, Set.mem_singleton_iff] at hx
            have hB := (Prod.mk.inj hx).2
            unfold hasFiredAuthPrin; rw [hB]; simp [hSlot]
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun uSk => ?_)
        unfold pqxdhAuthFgLatchedPreImpl1Key fgPreAuthInitPrin1Key liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

/-- Pre-sampling the target identity and SPK scalars preserves the distribution of
`runAuthFgLatchedSim1Key`. -/
theorem evalDist_runAuthFgLatchedSim1Key_eq_preSample_dh1 {S : Setup}
    (uIdx bIdx : ℕ) (P : Primitives) (A : AuthAdversary S)
    (obs : Bool × Bool × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := AuthFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runAuthFgLatchedSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runAuthFgLatchedSim1Key
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
        pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) none S P) A.run).run
          (AuthFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) P
      A.run (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh1_pqxdhAuthFgLatchedPreImpl1Key uIdx bIdx none P A.run
    (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhAuthFgLatchedPreImpl1Key_none_none_eq]
  simp only [pure_bind]

end Proofs.SignalPqxdh.Security
