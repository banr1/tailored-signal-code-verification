/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyC0
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c5
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-key `Auth` bad-signature hop: step map and pre-sampling

**Checked by Lean.** Relates one step of `pqxdhAuthSigPreImpl1Key` via `clearAuthWon` to
`pqxdhAuthFgLatchedPreImpl1Key` while not yet won, and proves that pre-sampling principal `k`'s
identity scalar preserves the distribution of the frozen one-key `Exact` game.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-! ## Step map -/

private theorem map_eq_self_of_support {α : Type} (mx : ProbComp α) (f : α → α)
    (hf : ∀ x ∈ support mx, f x = x) : f <$> mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp [hf a (by simp)]
  | query_bind i k ih =>
    rw [map_eq_bind_pure_comp, bind_assoc]; simp only [← map_eq_bind_pure_comp]
    congr 1; funext u
    exact ih u (fun x hx => hf x (by
      rw [MonadAttach.mem_support_bind]
      exact ⟨u, by simp, hx⟩))

theorem map_clearAuthWon_frozenExact_eq_kosk (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (q : AuthQuery S) (st : AuthState S)
    (hWon : st.hasWonAuth = false) :
    Prod.map id clearAuthWon <$>
      (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P) q).run st =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid st) := by
  have h := map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_mkG3Hybrid S P hP q st hWon
  have hComp : (Prod.map (α₁ := (authSpec S).Range q) id
      (fun h : AuthHybridState S => clearAuthWon h.base)) =
      fun a => Prod.map id clearAuthWon (Prod.map id AuthHybridState.base a) := by
    funext ⟨r, h⟩; rfl
  rw [hComp, ← Functor.map_map, map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q (mkG3Hybrid st)]
    at h
  exact h

theorem map_base_pqxdhAuthFgLatchedImpl_eq_kosk (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S) :
    Prod.map id AuthFgCutoffState.base <$> (pqxdhAuthFgLatchedImpl S P q).run hst =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base) := by
  cases q <;>
    simp [pqxdhAuthFgLatchedImpl, pqxdhAuthFgImpl, StateT.run_mk] <;> rfl

theorem pqxdhAuthFgLatchedPreImpl_true_eq_latched (k bIdx : ℕ) (optSk : Option Bytes)
    (S : Setup) (P : Primitives) (q : AuthQuery S) :
    pqxdhAuthFgLatchedPreImpl true k bIdx optSk none S P q =
      pqxdhAuthFgLatchedImpl S P q ∨ ∃ u, q = .initPrin u := by
  cases optSk with
  | none => exact Or.inl (pqxdhAuthFgLatchedPreImpl_none_none true k bIdx S P q)
  | some sk =>
    have hSend : fgPreAuthSendHybrid .g3 true true k (some sk) S P =
        fgPreAuthSendHybrid .g3 true true k none S P := by
      funext sid u bundle m0 m1
      unfold fgPreAuthSendHybrid
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine (em (∃ u, q = .initPrin u)).elim Or.inr (fun hq => Or.inl ?_)
    rw [← pqxdhAuthFgLatchedPreImpl_none_none true k bIdx S P]
    cases q with
    | initPrin u => exact absurd ⟨u, rfl⟩ hq
    | sendOPK u i bundle m0 m1 =>
      simp only [pqxdhAuthFgLatchedPreImpl, pqxdhAuthFgPreImpl, hSend]
    | sendNoOPK u i bundle m0 m1 =>
      simp only [pqxdhAuthFgLatchedPreImpl, pqxdhAuthFgPreImpl, hSend]
    | _ => rfl

theorem fgPreAuthInitPrin1Key_pres_hasWonAuth (prinFlag : Bool) (prinIdx : ℕ)
    (optSk : Option Bytes) (S : Setup) (P : Primitives) (u : Fin S.N_id) (st : AuthState S) :
    PreservesAt AuthState.hasWonAuth st (fgPreAuthInitPrin1Key prinFlag prinIdx optSk S P u) := by
  intro x hx
  unfold fgPreAuthInitPrin1Key at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  revert hx
  cases st.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    rintro ⟨sk, _, rfl⟩; rfl
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    rintro rfl; rfl

/-- General step map (any `optSk`). -/
theorem map_clearAuthWon_authSigPre1Key_eq_fgPre_opt (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (optSk : Option Bytes) (q : AuthQuery S)
    (hst : AuthFgCutoffState S) (hWon : hst.base.hasWonAuth = false) :
    Prod.map id clearAuthWon <$> (pqxdhAuthSigPreImpl1Key k optSk S P q).run hst.base =
    Prod.map id AuthFgCutoffState.base <$>
      (pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot optSk none S P q).run hst := by
  by_cases hq : ∃ u, q = .initPrin u
  · obtain ⟨u, rfl⟩ := hq
    have hL : (pqxdhAuthSigPreImpl1Key k optSk S P (.initPrin u)).run hst.base =
        (fgPreAuthInitPrin1Key true k optSk S P u).run hst.base := by
      simp [pqxdhAuthSigPreImpl1Key, freezeImpl, StateT.run_bind, StateT.run_get, hWon]
    rw [hL, map_eq_self_of_support _ _ (fun x hx => by
      rcases x with ⟨r, s'⟩
      simp [Prod.map, clearAuthWon_of_hasWonAuth_false s'
        ((fgPreAuthInitPrin1Key_pres_hasWonAuth true k optSk S P u hst.base (r, s') hx).trans
          hWon)])]
    simp [pqxdhAuthFgLatchedPreImpl1Key, liftAuthFgBase, StateT.run_mk, Prod.map]
  · have hne : ∀ u, q ≠ .initPrin u := fun u h => hq ⟨u, h⟩
    rw [pqxdhAuthSigPreImpl1Key_of_not_initPrin k optSk S P q hne,
      pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true k S.N_spk_tot optSk none P q hne]
    have hFr : (pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P) q).run
        hst.base = (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P) q).run
        hst.base := by
      unfold pqxdhAuthWithProvFrozenImpl1Key pqxdhAuthWithProvFrozenImpl freezeImpl
      rw [pqxdhAuthWithProvImpl1Key_eq_of_ne_initPrin S P _ q hne]
    rcases pqxdhAuthFgLatchedPreImpl_true_eq_latched k S.N_spk_tot optSk S P q with h | h
    · rw [hFr, h, map_clearAuthWon_frozenExact_eq_kosk S P hP q hst.base hWon,
        map_base_pqxdhAuthFgLatchedImpl_eq_kosk]
    · exact absurd h hq

theorem map_clearAuthWon_authSigPre1Key_eq_fgPre (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (q : AuthQuery S)
    (hst : AuthFgCutoffState S) (hWon : hst.base.hasWonAuth = false) :
    Prod.map id clearAuthWon <$> (pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base =
    Prod.map id AuthFgCutoffState.base <$>
      (pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot (some sk) none S P q).run hst :=
  map_clearAuthWon_authSigPre1Key_eq_fgPre_opt S P hP k (some sk) q hst hWon

theorem hasWonAuth_false_of_mem_support_fgPre1Key_opt (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (optSk : Option Bytes) (q : AuthQuery S)
    (hst : AuthFgCutoffState S) (hWon : hst.base.hasWonAuth = false) :
    ∀ x ∈ support
      ((pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot optSk none S P q).run hst),
      x.2.base.hasWonAuth = false := by
  intro x hx
  have hmem : Prod.map id AuthFgCutoffState.base x ∈ support
      (Prod.map id AuthFgCutoffState.base <$>
        (pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot optSk none S P q).run hst) :=
    (by rw [support_map]; exact Set.mem_image_of_mem _ hx)
  rw [← map_clearAuthWon_authSigPre1Key_eq_fgPre_opt S P hP k optSk q hst hWon,
    support_map] at hmem
  obtain ⟨y, _, hy⟩ := hmem
  have h2 := congrArg Prod.snd hy
  simp only [Prod.map] at h2
  rw [← h2]; rfl

theorem hasWonAuth_false_of_mem_support_fgPre1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (q : AuthQuery S)
    (hst : AuthFgCutoffState S) (hWon : hst.base.hasWonAuth = false) :
    ∀ x ∈ support
      ((pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot (some sk) none S P q).run hst),
      x.2.base.hasWonAuth = false :=
  hasWonAuth_false_of_mem_support_fgPre1Key_opt S P hP k (some sk) q hst hWon

/-! ## Pre-sampling the target identity scalar -/

/-- "Fired" predicate for the pre-sampling slot: won, or principal `k` already exists. -/
def authSigPreFired (k : ℕ) {S : Setup} (st : AuthState S) : Prop :=
  st.hasWonAuth = true ∨ st.principals.any (fun (idx, _) => idx == k) = true

theorem pqxdhAuthSigPreImpl1Key_run_of_won (k : ℕ) (optSk : Option Bytes) (S : Setup)
    (P : Primitives) (q : AuthQuery S) (st : AuthState S) (hWon : st.hasWonAuth = true) :
    (pqxdhAuthSigPreImpl1Key k optSk S P q).run st = pure (.noneResp, st) := by
  simp [pqxdhAuthSigPreImpl1Key, freezeImpl, StateT.run_bind, StateT.run_get, hWon]

theorem pqxdhAuthSigPreImpl1Key_preserves_fired (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (optSk : Option Bytes) (q : AuthQuery S)
    (st : AuthState S) (hF : authSigPreFired k st) :
    ∀ x ∈ support ((pqxdhAuthSigPreImpl1Key k optSk S P q).run st), authSigPreFired k x.2 := by
  intro x hx
  cases hWon : st.hasWonAuth with
  | true =>
    rw [pqxdhAuthSigPreImpl1Key_run_of_won k optSk S P q st hWon] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact hF
  | false =>
    have hPrin : st.principals.any (fun (idx, _) => idx == k) = true := by
      rcases hF with h | h
      · rw [hWon] at h; exact absurd h (by simp)
      · exact h
    have hmem : Prod.map id clearAuthWon x ∈ support
        (Prod.map id clearAuthWon <$> (pqxdhAuthSigPreImpl1Key k optSk S P q).run st) :=
      (by rw [support_map]; exact Set.mem_image_of_mem _ hx)
    let hst : AuthFgCutoffState S := { base := st }
    rw [show st = hst.base from rfl,
      map_clearAuthWon_authSigPre1Key_eq_fgPre_opt S P hP k optSk q hst hWon,
      support_map] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hFired : hasFiredAuthPrin S k y.2 :=
      (pqxdhAuthFgLatchedPreImpl1Key_preserves_hasFired true k S.N_spk_tot optSk none P q hst
        y hy).2.1 k hPrin
    have h2 := congrArg Prod.snd hyx
    simp only [Prod.map] at h2
    right
    unfold hasFiredAuthPrin at hFired
    rw [h2] at hFired
    exact hFired

theorem evalDist_authSigPerK_lhs_eq_preSample (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ)
    (A : AuthAdversary S) (obs : AuthState S → Bool) :
    𝒟[runAuthWithProvFrozen1Key (checkBundleProvenanceExact P) S P A >>= fun (_, _, s) =>
      pure (obs s)] =
    𝒟[do
      let sk ← sampleScalar32
      let secb ← $ᵗ Bool
      let (_, s) ← (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthState S) ProbComp) + pqxdhAuthSigPreImpl1Key k (some sk) S P) A.run).run
          (AuthState.empty S secb)
      pure (obs s)] := by
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  unfold runAuthWithProvFrozen1Key
  simp only [bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  rw [← pqxdhAuthSigPreImpl1Key_none k S P]
  symm
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (authSigPreFired k)
    (pqxdhAuthSigPreImpl1Key k none S P)
    (fun sk => pqxdhAuthSigPreImpl1Key k (some sk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      pqxdhAuthSigPreImpl1Key_preserves_fired S P hP k none q s hFired x hx⟩)
    (fun q s hNF => ?_)
    A.run (AuthState.empty S secb) (fun x => pure (obs x.2))
  · intro sk
    cases hWon : s.hasWonAuth with
    | true =>
      rw [pqxdhAuthSigPreImpl1Key_run_of_won k _ S P q s hWon,
        pqxdhAuthSigPreImpl1Key_run_of_won k _ S P q s hWon]
    | false =>
      have hPrin : s.principals.any (fun (idx, _) => idx == k) = true := by
        rcases hFired with h | h
        · rw [hWon] at h; exact absurd h (by simp)
        · exact h
      cases q with
      | initPrin u =>
        simp only [pqxdhAuthSigPreImpl1Key, freezeImpl, fgPreAuthInitPrin1Key, StateT.run_bind,
          StateT.run_get, pure_bind, hWon, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
        by_cases hSlot : (u.val == k) = true
        · have hany : s.principals.any (fun (idx, _) => idx == u.val) = true := by
            rw [beq_iff_eq.mp hSlot]; exact hPrin
          simp [hany]
        · cases s.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
      | _ => rfl
  · have hWon : s.hasWonAuth = false := by
      cases h : s.hasWonAuth
      · rfl
      · exact absurd (Or.inl h) hNF
    have hPrin : s.principals.any (fun (idx, _) => idx == k) = false := by
      cases h : s.principals.any (fun (idx, _) => idx == k)
      · rfl
      · exact absurd (Or.inr h) hNF
    cases q with
    | initPrin u =>
      by_cases hSlot : (u.val == k) = true
      · have hany : s.principals.any (fun (idx, _) => idx == u.val) = false := by
          rw [beq_iff_eq.mp hSlot]; exact hPrin
        simp only [pqxdhAuthSigPreImpl1Key, freezeImpl, fgPreAuthInitPrin1Key, StateT.run_bind,
          StateT.run_get, pure_bind, hWon, hany, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
          hSlot]
        refine Or.inr ⟨fun obs' => ?_, fun sk x hx => ?_⟩
        · simp only [StateT.run_pure, StateT.run_monadLift,
            monadLift_self, StateT.run_set, pure_bind, bind_assoc]
        · simp only [StateT.run_pure, StateT.run_monadLift,
            monadLift_self, StateT.run_set, pure_bind,
            support_pure, Set.mem_singleton_iff] at hx
          have hB := (Prod.mk.inj hx).2
          right; rw [hB]; simp [hSlot]
      · refine Or.inl (fun sk => ?_)
        simp only [pqxdhAuthSigPreImpl1Key, freezeImpl, fgPreAuthInitPrin1Key, StateT.run_bind,
          StateT.run_get, pure_bind, hWon, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
        cases s.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

end Proofs.SignalPqxdh.Security
