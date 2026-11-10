/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdClear
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-key `Auth` Case A (`DH1`) `GapDhWithSign` bound

**Checked by Lean.** Bounds the per-index Case A (`DH1`) bad event of the one-key latched `.g3`
simulation `runAuthFgLatchedSim1Key` by the `GapDhWithSign` advantage of
`fgAuth1KeyGapDhAdvAt true uIdx bIdx`. The step coupling maintains a ghost two-key simulator state
related by `clearAuthSecSign uIdx`, signing the target principal's bundles via the `GapDhWithSign`
signing oracle within `sigBudget` and delegating all other steps to
`fgAuthStepCoupling_dh1_latched`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

open AuthDh3

/-! ## Reference step auxiliary invariant -/

/-- Auxiliary preservation relation across one non-`.initPrin` reference step. -/
def PreStepPreservesAuth1KeyAux {S : Setup} (hst hst' : AuthFgCutoffState S) : Prop :=
  ((∀ kv ∈ hst.base.principals, kv.2.secIKAsign = kv.2.secIKA0) →
    ∀ kv ∈ hst'.base.principals, kv.2.secIKAsign = kv.2.secIKA0) ∧
  (∀ k, (bundleSignedMessages k hst.base.spkBundles).length ≤
    (bundleSignedMessages k hst'.base.spkBundles).length) ∧
  (∀ k j, hst.base.spkBundles.any (fun (k', _) => k' == (k, j)) = false →
    hst'.base.spkBundles.any (fun (k', _) => k' == (k, j)) = true →
    (bundleSignedMessages k hst.base.spkBundles).length + 2 ≤
      (bundleSignedMessages k hst'.base.spkBundles).length)

theorem preStepPreservesAuth1KeyAux_of_eq {S : Setup} {hst hst' : AuthFgCutoffState S}
    (hPrin : hst'.base.principals = hst.base.principals)
    (hSpk : hst'.base.spkBundles = hst.base.spkBundles) :
    PreStepPreservesAuth1KeyAux hst hst' :=
  ⟨fun h kv hkv => h kv (hPrin ▸ hkv), fun _ => hSpk ▸ Nat.le_refl _,
    fun _ _ hF hT => by rw [hSpk, hF] at hT; cases hT⟩

theorem preStepPreservesAuth1KeyAux_of_base_eq {S : Setup} {hst hst' hst'' : AuthFgCutoffState S}
    (hBase : hst''.base = hst'.base) (h : PreStepPreservesAuth1KeyAux hst hst') :
    PreStepPreservesAuth1KeyAux hst hst'' := by
  unfold PreStepPreservesAuth1KeyAux; rw [hBase]; exact h

theorem pqxdhAuthFgPreImpl_preserves_1KeyAux_of_ne_initPrin {S : Setup} (P : Primitives)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes) (q : AuthQuery S) (hq : ∀ u, q ≠ .initPrin u)
    (hst : AuthFgCutoffState S) :
    ∀ x ∈ support ((pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst),
      PreStepPreservesAuth1KeyAux hst x.2 := by
  have hUnchanged : ∀ x : AuthResponse × AuthFgCutoffState S,
      x.2.base.principals = hst.base.principals → x.2.base.spkBundles = hst.base.spkBundles →
      PreStepPreservesAuth1KeyAux hst x.2 := fun x hP hS => preStepPreservesAuth1KeyAux_of_eq hP hS
  intro x hx
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | corruptIK u =>
    change x ∈ support ((liftAuthFgHybrid
      (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true S P (.corruptIK
          u)))).run hst) at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩; unfold pqxdhAuthImpl at hb
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact hUnchanged x (by rw [(Prod.mk.inj hEq).2]) (by rw [(Prod.mk.inj hEq).2])
    | some pu =>
      rcases pu with ⟨_, _⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      refine ⟨fun hSec kv hkv => ?_, fun _ => by rw [hB], fun _ _ hF hT => ?_⟩
      · rw [hB] at hkv
        rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hMapEq⟩
        have h0 := hSec (idx, e) heMem
        by_cases hIdx : (idx == u.val) = true <;>
          simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hMapEq <;>
          (subst hMapEq; exact h0)
      · rw [hB] at hT; dsimp only at hT; rw [hF] at hT; cases hT
  | genSPK u j =>
    unfold pqxdhAuthFgPreImpl at hx; dsimp only at hx; rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩; unfold fgPreAuthGenSPK at hb
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
    cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact hUnchanged x (by rw [(Prod.mk.inj hEq).2]) (by rw [(Prod.mk.inj hEq).2])
      | some p =>
        rcases p with ⟨_, _⟩
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff]
        rintro ⟨_, _, _, _, _, _, _, _, hEq⟩
        have hB := (Prod.mk.inj hEq).2
        refine ⟨fun hSec kv hkv => hSec kv (by rw [hB] at hkv; exact hkv), fun k => ?_,
          fun k j' hF hT => ?_⟩
        · rw [hB]
          by_cases hku : u.val = k
          · subst hku
            rw [bundleSignedMessages_cons_eq, List.length_cons, List.length_cons]
            omega
          · rw [bundleSignedMessages_cons_of_ne k u.val j.val _ _ (beq_eq_false_iff_ne.mpr hku)]
        · rw [hB] at hT ⊢
          by_cases hKey : (u.val, j.val) = (k, j')
          · rcases Prod.mk.inj hKey with ⟨rfl, rfl⟩
            rw [bundleSignedMessages_cons_eq, List.length_cons, List.length_cons]
          · simp only [List.any_cons] at hT
            rw [hF] at hT
            simp only [Bool.or_false, beq_iff_eq] at hT
            exact absurd hT hKey
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact hUnchanged x (by rw [(Prod.mk.inj hEq).2]) (by rw [(Prod.mk.inj hEq).2])
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl at hx
    by_cases hOpt : bundle.opkB?.isNone = true
    · unfold liftAuthFgHybrid mkG3Hybrid at hx
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      exact hUnchanged x (by rw [(Prod.mk.inj hx).2]) (by rw [(Prod.mk.inj hx).2])
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isNone then return .noneResp
          fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendOPK u i) u bundle m0 m1)).run
            hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendOPK u i) u
            bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq] at hx
      rcases fgPreAuthSendHybrid_support true uIdx (some uSk) P (.sendOPK u i) u bundle m0 m1 hst x
        hx with ⟨hP, hS, _⟩
      exact hUnchanged x hP hS
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl at hx
    by_cases hOpt : bundle.opkB?.isSome = true
    · unfold liftAuthFgHybrid mkG3Hybrid at hx
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      exact hUnchanged x (by rw [(Prod.mk.inj hx).2]) (by rw [(Prod.mk.inj hx).2])
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isSome then return .noneResp
          fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendNoOPK u i) u bundle m0
            m1)).run hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendNoOPK u i) u
            bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq] at hx
      rcases fgPreAuthSendHybrid_support true uIdx (some uSk) P (.sendNoOPK u i) u bundle m0 m1 hst
        x hx with ⟨hP, hS, _⟩
      exact hUnchanged x hP hS
  | _ =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P _ (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, _, _⟩
    exact hUnchanged x hP hS

theorem pqxdhAuthFgLatchedPreImpl1Key_preserves_1KeyAux_of_ne_initPrin {S : Setup}
    (P : Primitives) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (q : AuthQuery S)
    (hq : ∀ u, q ≠ .initPrin u) (hst : AuthFgCutoffState S) :
    ∀ x ∈ support
      ((pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst),
      PreStepPreservesAuth1KeyAux hst x.2 := by
  intro x hx
  rw [pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P q hq]
    at hx
  rcases exists_support_pqxdhAuthFgPreImpl_of_latched true uIdx bIdx (some uSk) (some vSk) P q hst
    x hx with ⟨x0, hx0, _, hBaseEq, _, _⟩
  exact preStepPreservesAuth1KeyAux_of_base_eq hBaseEq.symm
    (pqxdhAuthFgPreImpl_preserves_1KeyAux_of_ne_initPrin P uIdx bIdx uSk vSk q hq hst x0 hx0)

/-! ## Extraction, halting, and dead-flag preservation -/

theorem lookupSenderIkPk_map_clearTargetPrinSecSign (tIdx sIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) :
    lookupSenderIkPk (principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)))
      sIdx = lookupSenderIkPk principals sIdx := by
  unfold lookupSenderIkPk
  rw [find?_idx_map_clearTargetPrinSecSign]
  cases principals.find? (fun (idx, _) => idx == sIdx) with
  | none => rfl
  | some p => rcases p with ⟨_, e⟩; exact clearTargetPrinSecSign_ikAPk _ _ _

theorem initAuthDh1Cand_clearTargetPrinSecSign {S : Setup} (P : Primitives) (tIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes)) :
    initAuthDh1Cand S P (principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)))
      spkBundles advKeyPows = initAuthDh1Cand S P principals spkBundles advKeyPows := by
  funext s; unfold initAuthDh1Cand; rw [lookupSenderIkPk_map_clearTargetPrinSecSign]

theorem pureExtractCdhFromAuthSimState_clearAuthSecSign {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (tIdx : ℕ)
    (st : FgAuthSimState S) :
    pureExtractCdhFromAuthSimState S P ddh useDh1 maxLen U V (clearAuthSecSign tIdx st) =
      pureExtractCdhFromAuthSimState S P ddh useDh1 maxLen U V st := by
  unfold pureExtractCdhFromAuthSimState
  simp only [clearAuthSecSign_advRoLog, clearAuthSecSign_respRecs, clearAuthSecSign_base_sessions,
    clearAuthSecSign_base_spkBundles, clearAuthSecSign_advKeyPows,
    clearAuthSecSign_base_principals, initAuthDh1Cand_clearTargetPrinSecSign]

theorem evalDist_simulateQ_fgAuth1KeySimImpl_halted {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (uIdx bIdx maxLen : ℕ) (U V : Bytes) {α : Type}
    (oa : OracleComp (unifSpec + authSpec S) α) (obs : FgAuth1KeySimState S → ProbComp Bool)
    (st : FgAuth1KeySimState S) (hCorr : isTargetPrinCorrupted uIdx st.sim = true) :
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (FgAuth1KeySimState S) ProbComp) +
      fgAuth1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V
    𝒟[(simulateQ full2 oa).run st >>= fun x => obs x.2] {true} = 𝒟[obs st] {true} := by
  intro full2; induction oa using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full2]; rw [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_const_of_support _ _ (𝒟[obs st] {true}) (fun u _ => ih u)
    · dsimp only [full2]
      have hHalt : (fgAuth1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V gq).run st =
          pure (.noneResp, st) := by
        unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure; simp [hCorr]
      rw [simulateQ_run_query_inr, hHalt, pure_bind]; exact ih .noneResp

theorem pqxdhAuthFgLatchedPreImpl1Key_preserves_deadAndUnlatchedDh1 {S : Setup} (P : Primitives)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes) (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (hD : deadAndUnlatchedDh1 uIdx bIdx hst = true) :
    ∀ x ∈ support
      ((pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadAndUnlatchedDh1 uIdx bIdx x.2 = true := by
  intro x hx
  by_cases hq : ∀ u, q ≠ .initPrin u
  · rw [pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P q hq]
      at hx
    exact pqxdhAuthFgLatchedPreImpl_preserves_deadAndUnlatchedDh1 P uIdx bIdx uSk vSk q hst hD x hx
  · push Not at hq; rcases hq with ⟨u, rfl⟩
    unfold deadAndUnlatchedDh1 at hD; rcases Bool.and_eq_true_iff.mp hD with ⟨hDead, hNotC⟩
    have hDead0 := hDead; unfold deadAuthDh1 at hDead
    cases hFP : hst.base.principals.find? (fun (u, _) => u == uIdx) with
    | none => rw [hFP] at hDead; cases hDead
    | some p0 =>
      rcases p0 with ⟨u0, uEntry0⟩; rw [hFP] at hDead; dsimp only at hDead
      have hu0Mem : (u0, uEntry0) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
      have hu0Eq : u0 = uIdx := beq_iff_eq.mp (List.find?_some
        (p := fun (x : Nat × PrincipalEntry) => x.1 == uIdx) hFP)
      subst hu0Eq
      unfold pqxdhAuthFgLatchedPreImpl1Key at hx
      rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
      have hL : x.2.latchedDh1 = hst.latchedDh1 := by
        unfold liftAuthFgBase at hx
        simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hx
        rcases hx with ⟨_, _, rfl⟩; rfl
      unfold fgPreAuthInitPrin1Key at hb
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
      cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
      · have hNe : (u.val == u0) = false := by
          cases hEqB : (u.val == u0)
          · rfl
          · have hT : (u0 == u.val) = true := by rw [beq_iff_eq] at hEqB ⊢; exact hEqB.symm
            have hAnyT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
              List.any_eq_true.mpr ⟨(u0, uEntry0), hu0Mem, hT⟩
            rw [hAny] at hAnyT; cases hAnyT
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
        rintro ⟨_, _, hEq⟩
        have hB := (Prod.mk.inj hEq).2
        unfold deadAndUnlatchedDh1 deadAuthDh1; rw [hL, hNotC, hB]; dsimp only [List.find?]
        rw [hNe, hFP]; simpa using hDead
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq
        unfold deadAndUnlatchedDh1
        rw [deadAuthDh1_eq_of_principals u0 (hst1 := hst) (hst2 := x.2)
          (by rw [(Prod.mk.inj hEq).2]), hDead0, hL, hNotC]; rfl

/-! ## Simulation invariant -/

/-- One-key Case A simulation invariant coupling `st` to a ghost two-key state via
`clearAuthSecSign uIdx`. -/
def FgAuthSimInvDh1Latched1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S) : Prop :=
  ∃ stGhost : FgAuthSimState S,
    st.sim = clearAuthSecSign uIdx stGhost ∧
    FgAuthSimInvDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst stGhost ∧
    2 * min S.N_spk_tot S.N_recv ≤
      (bundleSignedMessages uIdx hst.base.spkBundles).length + 2 * st.sigBudget ∧
    (∀ kv ∈ hst.base.principals, kv.2.secIKAsign = kv.2.secIKA0)

theorem fgAuthSimInvDh1Latched1Key_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (secb : Bool) :
    FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk b.q_total
      (AuthFgCutoffState.empty S secb) (FgAuth1KeySimState.empty S secb) :=
  ⟨FgAuthSimState.empty S secb, rfl,
    ⟨fgAuthSimInvDh1_empty S b P hP uIdx bIdx uSk vSk huSk hvSk secb, rfl⟩,
    by simp [AuthFgCutoffState.empty, FgAuth1KeySimState.empty, bundleSignedMessages],
    fun _ h => False.elim (List.not_mem_nil h)⟩

theorem fgAuthSimInvDh1Latched1Key_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (a : Bool) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st) :
    𝒟[(pure (badAuthFgDh1LatchedAt P maxLen uIdx bIdx hst) : ProbComp Bool)] {true} ≤
      𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P P.isValidDhTriple true b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) st.sim) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hInvL, _, _⟩
  have hDead : deadAuthDh1 uIdx hst = false := by
    unfold deadAndUnlatchedDh1 at hDF; rw [hInvL.2, Bool.not_false, Bool.and_true] at hDF
    exact hDF
  have hLatchEq : badAuthFgDh1LatchedAt P maxLen uIdx bIdx hst =
      badAuthFgDh1AtCore P maxLen uIdx bIdx hst.base hst.advRoLog hst.respRecs := by
    unfold badAuthFgDh1LatchedAt; rw [hInvL.2, Bool.false_or]; rfl
  rw [hLatchEq, hSimEq, pureExtractCdhFromAuthSimState_clearAuthSecSign]
  exact fgAuthSimInvDh1_terminal_le S b P hP maxLen uIdx bIdx uSk vSk huSk hvSk a rem hst stGhost
    hDead hInvL.1

/-! ## Delegated queries -/

theorem fgAuthStepPure_corruptIK_clearAuthSecSign_of_ne (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (u : Fin S.N_id)
    (hNe : (u.val == tIdx) = false) (st : FgAuthSimState S) :
    AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.corruptIK u)
      (clearAuthSecSign tIdx st) =
      (AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.corruptIK u) st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  dsimp only [AuthDh3.fgAuthStepPure]
  simp only [clearAuthSecSign_base_principals, find?_idx_map_clearTargetPrinSecSign]
  cases hF : st.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    dsimp only [Option.map]; simp only [pure_bind]
  | some p =>
    rcases p with ⟨u0, entry⟩
    dsimp only [Option.map]; simp only [pure_bind]
    have hu0 : u0 = u.val :=
      beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
    have hu0Ne : (u0 == tIdx) = false := by rw [hu0]; exact hNe
    have hEntry : clearTargetPrinSecSign tIdx u0 entry = entry := by
      unfold clearTargetPrinSecSign; simp [hu0Ne]
    rw [hEntry]
    have hMap :
        (st.base.principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).map
          (fun (idx, e) => if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) =
        (st.base.principals.map
          (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))).map
          (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) := by
      rw [List.map_map, List.map_map]
      congr 1; funext ⟨idx, e⟩
      dsimp only [Function.comp_def]
      unfold clearTargetPrinSecSign
      by_cases h1 : (idx == u.val) = true <;> by_cases h2 : (idx == tIdx) = true <;> simp [h1, h2]
    simp only [clearAuthSecSign, clearAuthSecSignBase, hMap]

theorem fgAuthStepPure_genSPK_clearAuthSecSign_of_ne (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hNe : (u.val == tIdx) = false) (st : FgAuthSimState S) :
    AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.genSPK u j)
      (clearAuthSecSign tIdx st) =
      (AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.genSPK u j) st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  dsimp only [AuthDh3.fgAuthStepPure]
  simp only [clearAuthSecSign_base_spkBundles, clearAuthSecSign_base_principals,
    find?_idx_map_clearTargetPrinSecSign]
  by_cases hAny : (st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
  · simp only [hAny, ↓reduceIte, pure_bind]
  · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
    cases hF : st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]; simp only [pure_bind]
    | some p =>
      rcases p with ⟨u0, uEntry⟩
      dsimp only [Option.map]
      have hu0 : u0 = u.val :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
      have hu0Ne : (u0 == tIdx) = false := by rw [hu0]; exact hNe
      have hEntry : clearTargetPrinSecSign tIdx u0 uEntry = uEntry := by
        unfold clearTargetPrinSecSign; simp [hu0Ne]
      rw [hEntry]
      simp only [bind_assoc, pure_bind]
      rfl

/-- Queries answered identically to the ghost two-key simulator up to `clearAuthSecSign tIdx`. -/
def isDelegatedAuth1KeyQuery {S : Setup} (tIdx : ℕ) : AuthQuery S → Bool
  | .initPrin _  => false
  | .corruptIK u => !(u.val == tIdx)
  | .genSPK u _  => !(u.val == tIdx)
  | _            => true

theorem fgAuthStepPure_clearAuthSecSign_delegated1Key (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S)
    (hq : isDelegatedAuth1KeyQuery tIdx q = true) (st : FgAuthSimState S) :
    AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q
        (clearAuthSecSign tIdx st) =
      (AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  cases q with
  | initPrin _ => cases hq
  | corruptIK u =>
    have hNe : (u.val == tIdx) = false := by simpa [isDelegatedAuth1KeyQuery] using hq
    exact fgAuthStepPure_corruptIK_clearAuthSecSign_of_ne P ddh useDh1 targetIdx targetSpkIdx tIdx
      S maxLen U V u hNe st
  | genSPK u j =>
    have hNe : (u.val == tIdx) = false := by simpa [isDelegatedAuth1KeyQuery] using hq
    exact fgAuthStepPure_genSPK_clearAuthSecSign_of_ne P ddh useDh1 targetIdx targetSpkIdx tIdx
      S maxLen U V u j hNe st
  | _ =>
    exact fgAuthStepPure_clearAuthSecSign P ddh useDh1 targetIdx targetSpkIdx tIdx S maxLen U V _
      rfl st

theorem fgAuth1KeySimImpl_true_run_delegated {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (uIdx bIdx maxLen : ℕ) (U V : Bytes)
    (q : AuthQuery S) (hq : isDelegatedAuth1KeyQuery uIdx q = true)
    (st : FgAuth1KeySimState S) (stGhost : FgAuthSimState S)
    (hSimEq : st.sim = clearAuthSecSign uIdx stGhost) :
    (fgAuth1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V q).run st =
      ((fgAuthSimImpl P ddh true uIdx bIdx S maxLen U V q).run stGhost >>=
        fun p => pure (p.1, { st with sim := clearAuthSecSign uIdx p.2 })) := by
  have hCorrEq : isTargetPrinCorrupted uIdx st.sim = isTargetPrinCorrupted uIdx stGhost := by
    rw [hSimEq, isTargetPrinCorrupted_clearAuthSecSign]
  have hRhs : (fgAuthSimImpl P ddh true uIdx bIdx S maxLen U V q).run stGhost =
      if isTargetPrinCorrupted uIdx stGhost then pure (.noneResp, stGhost) else
        AuthDh3.fgAuthStepPure P ddh true uIdx bIdx S maxLen U V q stGhost := by
    unfold fgAuthSimImpl fgAuthStepHalt
    by_cases hC : isTargetPrinCorrupted uIdx stGhost = true <;> simp [hC]
  rw [hRhs]
  cases hC : isTargetPrinCorrupted uIdx stGhost
  · have hStep : (fgAuth1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V q).run st =
        (AuthDh3.fgAuthStepPure P ddh true uIdx bIdx S maxLen U V q st.sim >>=
          fun p => pure (p.1, { st with sim := p.2 })) := by
      have hNC : isTargetPrinCorrupted uIdx st.sim = false := by rw [hCorrEq, hC]
      cases q with
      | initPrin _ => cases hq
      | genSPK u j =>
        have hNe : (u.val == uIdx) = false := by simpa [isDelegatedAuth1KeyQuery] using hq
        unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure fgAuthGenSPK1KeyPure
        simp [hNe, hNC]
      | _ =>
        unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure
        simp [hNC]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hStep, hSimEq, fgAuthStepPure_clearAuthSecSign_delegated1Key P ddh true uIdx bIdx uIdx S
      maxLen U V q hq stGhost]
    simp only [bind_assoc, pure_bind]
  · have hHalt : (fgAuth1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V q).run st =
        pure (.noneResp, st) := by
      have hCT : isTargetPrinCorrupted uIdx st.sim = true := by rw [hCorrEq, hC]
      unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure; simp [hCT]
    simp only [↓reduceIte, pure_bind, hHalt]
    congr 2
    cases st; dsimp only at hSimEq ⊢; rw [hSimEq]

/-! ## Step coupling -/

theorem fgAuthStepCoupling_dh1_delegated_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (q : AuthQuery S)
    (hDel : isDelegatedAuth1KeyQuery uIdx q = true) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true → 𝒟[k1 (r, hst')] {true} = 0)
    (hHaltCont : ∀ r st', isTargetPrinCorrupted uIdx st'.sim = true →
      𝒟[k2 (r, st')] {true} = 𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P
        P.isValidDhTriple true b.q_total (P.x25519Base uSk) (P.x25519Base vSk) st'.sim) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true}) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hNeInit : ∀ u, q ≠ .initPrin u := by
    intro u h; subst h; cases hDel
  rcases hInv with ⟨stGhost, hSimEq, hInvL, hBudget, hSecEq⟩
  let k1' : AuthResponse × AuthFgCutoffState S → ProbComp Bool :=
    open scoped Classical in
    fun p => if PreStepPreservesAuth1KeyAux hst p.2 then k1 p else pure false
  have hLhsEq :
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] =
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>=
        k1'] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    have hAux := pqxdhAuthFgLatchedPreImpl1Key_preserves_1KeyAux_of_ne_initPrin P uIdx bIdx uSk vSk
      q hNeInit hst x hx
    simp only [k1', hAux, ↓reduceIte]
  rw [hLhsEq, pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P
    q hNeInit, fgAuth1KeySimImpl_true_run_delegated P uSk P.isValidDhTriple uIdx bIdx b.q_total
    (P.x25519Base uSk) (P.x25519Base vSk) q hDel st stGhost hSimEq]
  simp only [bind_assoc, pure_bind]
  refine fgAuthStepCoupling_dh1_latched S b P hP uIdx bIdx uSk vSk huSk hvSk q rem hst stGhost hDF
    hInvL k1' (fun p => k2 (p.1, { st with sim := clearAuthSecSign uIdx p.2 }))
    (fun r hst' stGhost' hDF' hGInv' => ?_) (fun r hst' hDF' => ?_) (fun r stGhost' hC' => ?_)
  · dsimp only [k1']
    split_ifs with hAux
    · exact hCont r hst' { st with sim := clearAuthSecSign uIdx stGhost' } hDF'
        ⟨stGhost', rfl, hGInv', by dsimp only; have := hAux.2.1 uIdx; omega, hAux.1 hSecEq⟩
    · simp
  · dsimp only [k1']
    split_ifs with hAux
    · exact hDeadCont r hst' hDF'
    · simp
  · dsimp only
    rw [hHaltCont r { st with sim := clearAuthSecSign uIdx stGhost' }
      (by dsimp only; rw [isTargetPrinCorrupted_clearAuthSecSign]; exact hC')]
    dsimp only
    rw [pureExtractCdhFromAuthSimState_clearAuthSecSign]

theorem isTargetPrinCorrupted_eq_false_of_invDh1Latched (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuthSimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInvL : FgAuthSimInvDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st) :
    isTargetPrinCorrupted uIdx st = false := by
  have hDead : deadAuthDh1 uIdx hst = false := by
    unfold deadAndUnlatchedDh1 at hDF; rw [hInvL.2, Bool.not_false, Bool.and_true] at hDF
    exact hDF
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == uIdx) =
      (hst.base.principals.find? (fun (idx, _) => idx == uIdx)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hInvL.1.1.principals_eq]; exact find?_idx_erasePrincipalsFg uIdx uIdx _
  unfold isTargetPrinCorrupted; unfold deadAuthDh1 at hDead; rw [hPrinFind]
  cases hF : hst.base.principals.find? (fun (u0, _) => u0 == uIdx) with
  | none => rfl
  | some p =>
    rcases p with ⟨_, _⟩; rw [hF] at hDead
    simpa [erasePrincipalEntryFg_corrupted] using hDead

theorem evalDist_fgAuth1KeySimImpl_corruptIK_tgt_bind_eq (S : Setup) (b : QueryBudget)
    (P : Primitives) (uSk : Bytes) (uIdx bIdx : ℕ) (U V : Bytes) (W : Bytes) (u : Fin S.N_id)
    (hTgt : (u.val == uIdx) = true) (st : FgAuth1KeySimState S) (stGhost : FgAuthSimState S)
    (hSimEq : st.sim = clearAuthSecSign uIdx stGhost)
    (hNC : isTargetPrinCorrupted uIdx stGhost = false)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hHaltCont : ∀ r st', isTargetPrinCorrupted uIdx st'.sim = true →
      𝒟[k2 (r, st')] {true} = 𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P
        P.isValidDhTriple true b.q_total U V st'.sim) == W) : ProbComp Bool)] {true}) :
    𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total U V
        (.corruptIK u)).run st >>= k2] {true} =
      𝒟[(fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total U V (.corruptIK u)).run
          stGhost >>= fun p => if isTargetPrinCorrupted uIdx p.2 then
            (pure (P.pow8 (pureExtractCdhFromAuthSimState S P P.isValidDhTriple true b.q_total U V
              p.2) == W) : ProbComp Bool)
          else k2 (p.1, { st with sim := clearAuthSecSign uIdx p.2 })] {true} := by
  have hNC1 : isTargetPrinCorrupted uIdx st.sim = false := by
    rw [hSimEq, isTargetPrinCorrupted_clearAuthSecSign, hNC]
  have hL : (fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total U V
      (.corruptIK u)).run st =
      (AuthDh3.fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total U V (.corruptIK u)
        st.sim >>= fun p => pure (p.1, { st with sim := p.2 })) := by
    unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure
    simp [hNC1]
  have hR : (fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total U V (.corruptIK u)).run
      stGhost = AuthDh3.fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total U V
        (.corruptIK u) stGhost := by
    unfold fgAuthSimImpl fgAuthStepHalt; simp [hNC]
  rw [hL, hR, hSimEq]
  cases hF : stGhost.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    have hFc : (clearAuthSecSign uIdx stGhost).base.principals.find?
        (fun (idx, _) => idx == u.val) = none := by
      rw [clearAuthSecSign_base_principals, find?_idx_map_clearTargetPrinSecSign, hF]; rfl
    unfold AuthDh3.fgAuthStepPure; dsimp only; rw [hFc, hF]; simp only [pure_bind]
    simp [hNC]
  | some p =>
    rcases p with ⟨u0, entry⟩
    have hFc : (clearAuthSecSign uIdx stGhost).base.principals.find?
        (fun (idx, _) => idx == u.val) = some (u0, clearTargetPrinSecSign uIdx u0 entry) := by
      rw [clearAuthSecSign_base_principals, find?_idx_map_clearTargetPrinSecSign, hF]; rfl
    unfold AuthDh3.fgAuthStepPure; dsimp only; rw [hFc, hF]; simp only [pure_bind]
    refine (hHaltCont _ _ ?_).trans ?_
    · exact isTargetPrinCorrupted_map_corrupted_eq_true_of_eq uIdx u.val hTgt _ u0 _ hFc
    · rw [ite_eq_left (isTargetPrinCorrupted_map_corrupted_eq_true_of_eq uIdx u.val hTgt stGhost u0
        entry hF)]
      dsimp only
      rw [pureExtractCdhFromAuthSimState_corruptIK_eq, pureExtractCdhFromAuthSimState_corruptIK_eq,
        pureExtractCdhFromAuthSimState_clearAuthSecSign]

theorem fgAuthStepCoupling_dh1_corruptIK_tgt_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (u : Fin S.N_id)
    (hTgt : (u.val == uIdx) = true) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true → 𝒟[k1 (r, hst')] {true} = 0)
    (hHaltCont : ∀ r st', isTargetPrinCorrupted uIdx st'.sim = true →
      𝒟[k2 (r, st')] {true} = 𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P
        P.isValidDhTriple true b.q_total (P.x25519Base uSk) (P.x25519Base vSk) st'.sim) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true}) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run
        hst >>= k1] {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u)).run st >>= k2] {true} := by
  have hNeInit : ∀ u', (AuthQuery.corruptIK u : AuthQuery S) ≠ .initPrin u' := by
    intro u' h; cases h
  rcases hInv with ⟨stGhost, hSimEq, hInvL, hBudget, hSecEq⟩
  have hNC := isTargetPrinCorrupted_eq_false_of_invDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk
    (rem + 1) hst stGhost hDF hInvL
  let k1' : AuthResponse × AuthFgCutoffState S → ProbComp Bool :=
    open scoped Classical in
    fun p => if PreStepPreservesAuth1KeyAux hst p.2 then k1 p else pure false
  have hLhsEq :
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run
        hst >>= k1] =
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run
        hst >>= k1'] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    have hAux := pqxdhAuthFgLatchedPreImpl1Key_preserves_1KeyAux_of_ne_initPrin P uIdx bIdx uSk vSk
      _ hNeInit hst x hx
    simp only [k1', hAux, ↓reduceIte]
  rw [hLhsEq, pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P
    _ hNeInit, evalDist_fgAuth1KeySimImpl_corruptIK_tgt_bind_eq S b P uSk uIdx bIdx
    (P.x25519Base uSk) (P.x25519Base vSk) _ u hTgt st stGhost hSimEq hNC k2 hHaltCont]
  refine fgAuthStepCoupling_dh1_latched S b P hP uIdx bIdx uSk vSk huSk hvSk _ rem hst stGhost hDF
    hInvL k1' _ (fun r hst' stGhost' hDF' hGInv' => ?_) (fun r hst' hDF' => ?_)
    (fun r stGhost' hC' => ?_)
  · have hNC' := isTargetPrinCorrupted_eq_false_of_invDh1Latched S b P hP uIdx bIdx uSk vSk huSk
      hvSk rem hst' stGhost' hDF' hGInv'
    dsimp only [k1']
    rw [hNC']; simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hAux
    · exact hCont r hst' { st with sim := clearAuthSecSign uIdx stGhost' } hDF'
        ⟨stGhost', rfl, hGInv', by dsimp only; have := hAux.2.1 uIdx; omega, hAux.1 hSecEq⟩
    · simp
  · dsimp only [k1']
    split_ifs with hAux
    · exact hDeadCont r hst' hDF'
    · simp
  · dsimp only; rw [ite_eq_left hC']

theorem fgAuth1KeySimImpl_genSPK_tgt_run_eq {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (uIdx bIdx maxLen : ℕ) (U V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hTgt : (u.val == uIdx) = true)
    (st : FgAuth1KeySimState S) (stGhost : FgAuthSimState S)
    (hSimEq : st.sim = clearAuthSecSign uIdx stGhost)
    (hNC : isTargetPrinCorrupted uIdx stGhost = false)
    (hSign : ∀ u0 e, stGhost.base.principals.find? (fun (idx, _) => idx == u.val) = some (u0, e) →
      e.secIKAsign = uSk)
    (hBudgetPos : stGhost.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false →
      0 < st.sigBudget) :
    (fgAuth1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V (.genSPK u j)).run st =
      ((fgAuthSimImpl P ddh true uIdx bIdx S maxLen U V (.genSPK u j)).run stGhost >>=
        fun p => pure (p.1, FgAuth1KeySimState.mk (clearAuthSecSign uIdx p.2)
          (st.sigBudget -
            (if stGhost.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) then 0
             else if p.2.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) then 1 else 0)))) := by
  rcases st with ⟨sim, sb⟩
  dsimp only at hSimEq hBudgetPos ⊢
  subst hSimEq
  have hNC1 : isTargetPrinCorrupted uIdx (clearAuthSecSign uIdx stGhost) = false := by
    rw [isTargetPrinCorrupted_clearAuthSecSign, hNC]
  have hR : (fgAuthSimImpl P ddh true uIdx bIdx S maxLen U V (.genSPK u j)).run stGhost =
      AuthDh3.fgAuthStepPure P ddh true uIdx bIdx S maxLen U V (.genSPK u j) stGhost := by
    unfold fgAuthSimImpl fgAuthStepHalt; simp [hNC]
  rw [hR]
  unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure fgAuthGenSPK1KeyPure
  simp only [StateT_run_mk, hNC1, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
    hTgt, clearAuthSecSign_base_spkBundles, clearAuthSecSign_base_principals,
    find?_idx_map_clearTargetPrinSecSign]
  unfold AuthDh3.fgAuthStepPure
  cases hAny : stGhost.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · have hPos := hBudgetPos hAny
    have hAny' : (stGhost.base.spkBundles.any fun x => x.1 == (u.val, j.val)) = false := hAny
    simp only [Bool.false_eq_true, ↓reduceIte, hAny']
    cases hF : stGhost.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp [hAny']
    | some p =>
      rcases p with ⟨u0, e⟩
      have hS := hSign u0 e hF
      have hsb : (sb == 0) = false := by simp; omega
      dsimp only [Option.map]
      simp only [hsb, Bool.false_eq_true, ↓reduceIte, sampleKemKeyGen, bind_assoc, pure_bind, hS,
        clearTargetPrinSecSign_ikAPk, fgGapDh_spkBundleFlatIdx_eq, hAny', List.any_cons,
        beq_self_eq_true, Bool.true_or]
      rfl
  · have hAny' : (stGhost.base.spkBundles.any fun x => x.1 == (u.val, j.val)) = true := hAny
    simp [hAny']

theorem fgAuthStepCoupling_dh1_genSPK_tgt_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hTgt : (u.val == uIdx) = true) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true → 𝒟[k1 (r, hst')] {true} = 0)
    (hHaltCont : ∀ r st', isTargetPrinCorrupted uIdx st'.sim = true →
      𝒟[k2 (r, st')] {true} = 𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P
        P.isValidDhTriple true b.q_total (P.x25519Base uSk) (P.x25519Base vSk) st'.sim) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true}) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run
        hst >>= k1] {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j)).run st >>= k2] {true} := by
  have hNeInit : ∀ u', (AuthQuery.genSPK u j : AuthQuery S) ≠ .initPrin u' := by
    intro u' h; cases h
  have huEq : u.val = uIdx := beq_iff_eq.mp hTgt
  rcases hInv with ⟨stGhost, hSimEq, hInvL, hBudget, hSecEq⟩
  have hNC := isTargetPrinCorrupted_eq_false_of_invDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk
    (rem + 1) hst stGhost hDF hInvL
  rcases hInvL.1 with ⟨hBR, -, -, -, -, -, -, -, hValid, hPrins, -⟩
  have hAnyG : ∀ (stG : FgAuthSimState S) (h : AuthFgCutoffState S),
      FgAuthBaseRel true uIdx bIdx stG.base h.base →
      stG.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) =
        h.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) := by
    intro stG h hR; rw [hR.spkBundles_eq]; exact any_idx_eraseSpkBundlesFg S bIdx _ _
  have hA0 := hAnyG stGhost hst hBR
  have hSign : ∀ u0 e, stGhost.base.principals.find? (fun (idx, _) => idx == u.val) =
      some (u0, e) → e.secIKAsign = uSk := by
    intro u0 e hF
    have hPrinFind : stGhost.base.principals.find? (fun (idx, _) => idx == u.val) =
        (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
          (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
      rw [hBR.principals_eq]; exact find?_idx_erasePrincipalsFg uIdx u.val _
    rw [hPrinFind] at hF
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rw [hFP] at hF; cases hF
    | some q =>
      rcases q with ⟨u1, e1⟩
      rw [hFP] at hF
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at hF
      rcases hF with ⟨rfl, rfl⟩
      have hMem := List.mem_of_find?_eq_some hFP
      have hu1 : u1 = u.val := beq_iff_eq.mp
        (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFP)
      rw [erasePrincipalEntryFg_secIKAsign, hSecEq _ hMem]
      exact (hPrins _ hMem).2.2 (by dsimp only; rw [hu1]; exact hTgt)
  have hBudgetPos : stGhost.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) = false →
      0 < st.sigBudget := by
    intro hF
    rw [hA0] at hF
    let dummyB : SpkBundleEntry :=
      { spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
    have hLen := bundleSignedMessages_length_add_two_le S u j dummyB hst.base.spkBundles
      hValid.2.1 hF
    rw [huEq] at hLen
    omega
  let k1' : AuthResponse × AuthFgCutoffState S → ProbComp Bool :=
    open scoped Classical in
    fun p => if PreStepPreservesAuth1KeyAux hst p.2 then k1 p else pure false
  have hLhsEq :
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run
        hst >>= k1] =
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run
        hst >>= k1'] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    have hAux := pqxdhAuthFgLatchedPreImpl1Key_preserves_1KeyAux_of_ne_initPrin P uIdx bIdx uSk vSk
      _ hNeInit hst x hx
    simp only [k1', hAux, ↓reduceIte]
  rw [hLhsEq, pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P
    _ hNeInit, fgAuth1KeySimImpl_genSPK_tgt_run_eq P uSk P.isValidDhTriple uIdx bIdx b.q_total
    (P.x25519Base uSk) (P.x25519Base vSk) u j hTgt st stGhost hSimEq hNC hSign hBudgetPos]
  simp only [bind_assoc, pure_bind]
  refine fgAuthStepCoupling_dh1_latched S b P hP uIdx bIdx uSk vSk huSk hvSk _ rem hst stGhost hDF
    hInvL k1' _ (fun r hst' stGhost' hDF' hGInv' => ?_) (fun r hst' hDF' => ?_)
    (fun r stGhost' hC' => ?_)
  · dsimp only [k1']
    by_cases hAux : PreStepPreservesAuth1KeyAux hst hst'
    · rw [ite_eq_left hAux]
      refine hCont r hst' _ hDF' ⟨stGhost', rfl, hGInv', ?_, hAux.1 hSecEq⟩
      dsimp only
      have hA1 := hAnyG stGhost' hst' hGInv'.1.1
      have hMono := hAux.2.1 uIdx
      split_ifs with h1 h2
      · omega
      · rw [hA0] at h1; rw [hA1] at h2
        have h2' := hAux.2.2 u.val j.val (Bool.eq_false_iff.mpr h1) h2
        rw [huEq] at h2'
        omega
      · omega
    · rw [ite_eq_right hAux]; simp
  · dsimp only [k1']
    split_ifs with hAux
    · exact hDeadCont r hst' hDF'
    · simp
  · dsimp only
    rw [hHaltCont r _ (by dsimp only; rw [isTargetPrinCorrupted_clearAuthSecSign]; exact hC')]
    dsimp only
    rw [pureExtractCdhFromAuthSimState_clearAuthSecSign]

theorem any_idx_map_clearTargetPrinSecSign_auth (tIdx uVal : ℕ)
    (L : List (Nat × PrincipalEntry)) :
    (L.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).any
      (fun (idx, _) => idx == uVal) =
      L.any (fun (idx, _) => idx == uVal) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    simp only [List.map_cons, List.any_cons, ih]

theorem fgAuthStepCoupling_dh1_initPrin_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (u : Fin S.N_id) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.initPrin u)).run
        hst >>= k1] {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u)).run st >>= k2] {true} := by
  rcases st with ⟨sim, sb⟩
  rcases hInv with ⟨stGhost, hSimEq, hInvL, hBudget, hSecEq⟩
  dsimp only at hSimEq hBudget
  subst hSimEq
  have hNC := isTargetPrinCorrupted_eq_false_of_invDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk
    (rem + 1) hst stGhost hDF hInvL
  have hNC1 : isTargetPrinCorrupted uIdx (clearAuthSecSign uIdx stGhost) = false := by
    rw [isTargetPrinCorrupted_clearAuthSecSign, hNC]
  rcases hInvL with ⟨⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩, hLatch⟩
  have hPrinAnyEq : (clearAuthSecSign uIdx stGhost).base.principals.any
      (fun (idx, _) => idx == u.val) = hst.base.principals.any (fun (idx, _) => idx == u.val) := by
    rw [clearAuthSecSign_base_principals, any_idx_map_clearTargetPrinSecSign_auth, hBaseRel.principals_eq]
    exact any_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  unfold pqxdhAuthFgLatchedPreImpl1Key liftAuthFgBase fgPreAuthInitPrin1Key
  unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure fgAuthInitPrin1KeyPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and, hNC1,
    Bool.false_eq_true, ↓reduceIte, hPrinAnyEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hTgt : (u.val == uIdx) = true
    · have huEq : u.val = uIdx := beq_iff_eq.mp hTgt
      simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, evalDist_sampleScalar32_const]
      let entry1 : PrincipalEntry := {
        secIKA0 := uSk, ikAPk := P.x25519Base uSk,
        secIKAsign := uSk, ikSignPk := P.x25519Base uSk, corrupted := false }
      let entryG : PrincipalEntry := {
        secIKA0 := [], ikAPk := P.x25519Base uSk,
        secIKAsign := uSk, ikSignPk := P.x25519Base uSk, corrupted := false }
      let stGhost' : FgAuthSimState S :=
        { stGhost with base := { stGhost.base with
            principals := (u.val, entryG) :: stGhost.base.principals } }
      refine hCont _ _ _ ?_ ⟨stGhost', ?_, ⟨⟨⟨hBaseRel.secb_eq, ?_, hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq,
        hAdvEq, hCache, hRootCache, by dsimp only [stGhost']; omega, by dsimp only [stGhost']; omega,
        by dsimp only; omega,
        ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1, hValidEc.2.1,
          hValidEc.2.2.1, hValidEc.2.2.2⟩, ?_, hSpks, hOpks, hSess⟩, hLatch⟩, ?_, ?_⟩
      · unfold deadAndUnlatchedDh1 deadAuthDh1; dsimp only [List.find?]; rw [hTgt]; rfl
      · simp only [stGhost', entryG, clearAuthSecSign, clearAuthSecSignBase, List.map_cons,
          clearTargetPrinSecSign, hTgt, ↓reduceIte]
        try rfl
      · dsimp only [stGhost']; rw [hBaseRel.principals_eq]; unfold erasePrincipalsOptFg
        simp [erasePrincipalsFg, erasePrincipalEntryFg, entryG, huEq]
      · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨huSk, rfl, fun _ => rfl⟩
        · exact hPrins kv hMem
      · dsimp only; exact hBudget
      · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · rfl
        · exact hSecEq kv hMem
    · have hTgtF : (u.val == uIdx) = false := Bool.eq_false_iff.mpr hTgt
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun sk0 hSk0 => ?_)
      have hLen0 : sk0.length = 32 := length_of_mem_support_sampleScalar32 hSk0
      let entry1 : PrincipalEntry := {
        secIKA0 := sk0, ikAPk := P.x25519Base sk0,
        secIKAsign := sk0, ikSignPk := P.x25519Base sk0, corrupted := false }
      let stGhost' : FgAuthSimState S :=
        { stGhost with base := { stGhost.base with
            principals := (u.val, entry1) :: stGhost.base.principals } }
      refine hCont _ _ _ ?_ ⟨stGhost', ?_, ⟨⟨⟨hBaseRel.secb_eq, ?_, hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq,
        hAdvEq, hCache, hRootCache, by dsimp only [stGhost']; omega, by dsimp only [stGhost']; omega,
        by dsimp only; omega,
        ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1, hValidEc.2.1,
          hValidEc.2.2.1, hValidEc.2.2.2⟩, ?_, hSpks, hOpks, hSess⟩, hLatch⟩, ?_, ?_⟩
      · unfold deadAndUnlatchedDh1 at hDF ⊢; unfold deadAuthDh1 at hDF ⊢
        dsimp only [List.find?]; rw [hTgtF]; exact hDF
      · simp only [stGhost', entry1, clearAuthSecSign, clearAuthSecSignBase, List.map_cons,
          clearTargetPrinSecSign, hTgtF, Bool.false_eq_true, ↓reduceIte]
        try rfl
      · dsimp only [stGhost']; rw [hBaseRel.principals_eq]; unfold erasePrincipalsOptFg
        simp [erasePrincipalsFg, erasePrincipalEntryFg, beq_eq_false_iff_ne.mp hTgtF, entry1]
      · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen0, rfl, fun h => by rw [hTgtF] at h; cases h⟩
        · exact hPrins kv hMem
      · dsimp only; exact hBudget
      · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · rfl
        · exact hSecEq kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact hCont _ hst _ hDF ⟨stGhost, rfl, ⟨⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache,
      by omega, by omega, by omega, hValidEc, hPrins, hSpks, hOpks, hSess⟩, hLatch⟩, hBudget,
      hSecEq⟩

theorem fgAuthStepCoupling_dh1_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (q : AuthQuery S)
    (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true → 𝒟[k1 (r, hst')] {true} = 0)
    (hHaltCont : ∀ r st', isTargetPrinCorrupted uIdx st'.sim = true →
      𝒟[k2 (r, st')] {true} = 𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P
        P.isValidDhTriple true b.q_total (P.x25519Base uSk) (P.x25519Base vSk) st'.sim) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true}) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  cases q with
  | initPrin u =>
    exact fgAuthStepCoupling_dh1_initPrin_1Key S b P hP uIdx bIdx uSk vSk huSk hvSk u rem hst st
      hDF hInv k1 k2 hCont
  | corruptIK u =>
    by_cases hT : (u.val == uIdx) = true
    · exact fgAuthStepCoupling_dh1_corruptIK_tgt_1Key S b P hP uIdx bIdx uSk vSk huSk hvSk u hT
        rem hst st hDF hInv k1 k2 hCont hDeadCont hHaltCont
    · exact fgAuthStepCoupling_dh1_delegated_1Key S b P hP uIdx bIdx uSk vSk huSk hvSk _
        (by simpa [isDelegatedAuth1KeyQuery] using hT) rem hst st hDF hInv k1 k2 hCont hDeadCont
        hHaltCont
  | genSPK u j =>
    by_cases hT : (u.val == uIdx) = true
    · exact fgAuthStepCoupling_dh1_genSPK_tgt_1Key S b P hP uIdx bIdx uSk vSk huSk hvSk u j hT
        rem hst st hDF hInv k1 k2 hCont hDeadCont hHaltCont
    · exact fgAuthStepCoupling_dh1_delegated_1Key S b P hP uIdx bIdx uSk vSk huSk hvSk _
        (by simpa [isDelegatedAuth1KeyQuery] using hT) rem hst st hDF hInv k1 k2 hCont hDeadCont
        hHaltCont
  | _ =>
    exact fgAuthStepCoupling_dh1_delegated_1Key S b P hP uIdx bIdx uSk vSk huSk hvSk _ rfl rem hst
      st hDF hInv k1 k2 hCont hDeadCont hHaltCont

/-! ## Case A bound -/

/-- Bounds the per-index latched `DH1` bad event in `runAuthFgLatchedSim1Key` by the
`GapDhWithSign` advantage of `fgAuth1KeyGapDhAdvAt true uIdx bIdx`. -/
theorem prob_badAuthFgDh1LatchedAt_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (AuthAdversary S) b)
    (uIdx : ℕ) (_huIdx : uIdx ∈ Finset.range S.N_id) (bIdx : ℕ)
    (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
        pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2.2)] {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt true uIdx bIdx S b A) := by
  unfold GapDhWithSignReal GapDhWithSign; refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runAuthFgLatchedSim1Key_eq_preSample_dh1 uIdx bIdx P A.1 (fun x => pure
    (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2.2)), gapDhWithSignExp_fgAuth1KeyGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  let obs2 : FgAuth1KeySimState S → ProbComp Bool := fun s2 => pure (P.pow8
      (pureExtractCdhFromAuthSimState S P P.isValidDhTriple true b.q_total (P.x25519Base uSk)
      (P.x25519Base vSk) s2.sim) == P.pow8 (P.x25519 uSk (P.x25519Base vSk)))
  exact evalDist_simulateQ_le_of_step_or_dead_or_halt (deadAndUnlatchedDh1 uIdx bIdx)
      (fun s2 : FgAuth1KeySimState S => isTargetPrinCorrupted uIdx s2.sim)
      (FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huLen hvLen)
      (pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P)
      (fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total (P.x25519Base uSk)
        (P.x25519Base vSk))
      (fun x => pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2)) obs2
      (fun q s1 hD x hx =>
        pqxdhAuthFgLatchedPreImpl1Key_preserves_deadAndUnlatchedDh1 P uIdx bIdx uSk vSk q s1 hD x hx)
      (fun oa s2 hCorr => evalDist_simulateQ_fgAuth1KeySimImpl_halted P uSk P.isValidDhTriple uIdx
        bIdx b.q_total (P.x25519Base uSk) (P.x25519Base vSk) oa obs2 s2 hCorr)
      (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont hHaltCont =>
        fgAuthStepCoupling_dh1_1Key S b P hP uIdx bIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1
          k2 hCont hDeadCont hHaltCont)
      (fun a s1 hD => by
        simp [badAuthFgDh1LatchedAt_eq_false_of_deadAndUnlatchedDh1 P b.q_ro uIdx bIdx s1 hD])
      (fun a rem s1 s2 hDF hInv =>
        fgAuthSimInvDh1Latched1Key_terminal_le S b P hP b.q_ro uIdx bIdx uSk vSk huLen hvLen a rem
          s1 s2 hDF hInv)
      A.1.run b.q_total (QueryBounded.auth_total A.2)
      (AuthFgCutoffState.empty S secb) (FgAuth1KeySimState.empty S secb)
      (fgAuthSimInvDh1Latched1Key_empty S b P hP uIdx bIdx uSk vSk huLen hvLen secb)

end Proofs.SignalPqxdh.Security
