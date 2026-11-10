/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Auth1KeyStatements
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB3
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-key `Auth` bad-signature hop: frozen provenance games

**Checked by Lean.** Defines one-key provenance-parameterized games frozen upon `hasWonAuth` for the
`G0.1 → G1` bad-signature hop, and proves the game equivalences across `Orig`, `Dual`, and `Exact`
bundle provenance checks.
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
namespace Proofs.SignalPqxdh.Security

/-- One-key `pqxdhAuthWithProvImpl`: `.initPrin` from `pqxdhAuthImpl1Key`. -/
def pqxdhAuthWithProvImpl1Key (S : Setup) (P : Primitives) (provFn : ProvFnType) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) := fun q =>
  match q with
  | .initPrin u => pqxdhAuthImpl1Key S P (.initPrin u)
  | q => pqxdhAuthWithProvImpl S P provFn q

theorem pqxdhAuthWithProvImpl1Key_checkBundleProvenance (S : Setup) (P : Primitives) :
    pqxdhAuthWithProvImpl1Key S P (checkBundleProvenance P) = pqxdhAuthImpl1Key S P := by
  funext q
  cases q <;> rfl

theorem pqxdhAuthWithProvImpl1Key_eq_of_ne_initPrin (S : Setup) (P : Primitives)
    (provFn : ProvFnType) (q : AuthQuery S) (h : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthWithProvImpl1Key S P provFn q = pqxdhAuthWithProvImpl S P provFn q := by
  cases q <;> first | rfl | exact absurd rfl (h _)

theorem pqxdhAuthWithProvImpl1Key_commutes_mapAuthSessions (S : Setup) (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool)
    (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd))
    (q : AuthQuery S) (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    CommutesRel (mapAuthSessions mapEntry) st
      (pqxdhAuthWithProvImpl1Key S P prov1 q)
      (pqxdhAuthWithProvImpl1Key S P prov2 q) := by
  by_cases hq : ∃ u, q = .initPrin u
  · obtain ⟨u, rfl⟩ := hq
    intro mapEntry
    unfold pqxdhAuthWithProvImpl1Key pqxdhAuthImpl1Key
    apply CommutesRel.get_bind
    dsimp only [mapAuthSessions]
    repeat (first
      | apply CommutesRel.pure
      | (rw [pure_bind, pure_bind])
      | (apply CommutesRel.liftM_bind; intro _)
      | (apply CommutesRel.set_bind; rfl)
      | apply CommutesRel.ite
      | split)
  · have hne : ∀ u, q ≠ .initPrin u := fun u h => hq ⟨u, h⟩
    rw [pqxdhAuthWithProvImpl1Key_eq_of_ne_initPrin S P prov1 q hne,
      pqxdhAuthWithProvImpl1Key_eq_of_ne_initPrin S P prov2 q hne]
    exact pqxdhAuthWithProvImpl_commutes_mapAuthSessions S P f prov1 prov2 h_prov q st

theorem pqxdhAuthWithProvImpl1Key_hasWonAuth_sticky (S : Setup) (P : Primitives)
    (provFn : ProvFnType) (q : AuthQuery S) (st : AuthState S) (hWon : st.hasWonAuth = true) :
    ∀ x ∈ support ((pqxdhAuthWithProvImpl1Key S P provFn q).run st), x.2.hasWonAuth = true := by
  by_cases hq : ∃ u, q = .initPrin u
  · obtain ⟨u, rfl⟩ := hq
    have hPres : PreservesAt AuthState.hasWonAuth st
        (pqxdhAuthWithProvImpl1Key S P provFn (.initPrin u)) := by
      unfold pqxdhAuthWithProvImpl1Key pqxdhAuthImpl1Key; dsimp only; prove_preserves_at
    intro x hx; rw [hPres x hx, hWon]
  · rw [pqxdhAuthWithProvImpl1Key_eq_of_ne_initPrin S P provFn q (fun u h => hq ⟨u, h⟩)]
    exact pqxdhAuthWithProvImpl_hasWonAuth_sticky S P provFn q st hWon

/-- Frozen one-key provenance oracle. -/
def pqxdhAuthWithProvFrozenImpl1Key (S : Setup) (P : Primitives) (provFn : ProvFnType) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) :=
  freezeImpl AuthState.hasWonAuth (fun _ => .noneResp) (pqxdhAuthWithProvImpl1Key S P provFn)

noncomputable def runAuthWithProvFrozen1Key (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthState S) := do
  let secb ← $ᵗ Bool; let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthWithProvFrozenImpl1Key S P prov
  let (b', finalSt) ← (simulateQ impl A.run).run initSt; return (secb, b', finalSt)

noncomputable def authExpG0Frozen1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen1Key (checkBundleProvenance P) S P A >>= contAuth S P

noncomputable def authExpG0_1WithProvFrozen1Key (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen1Key prov S P A >>= fun a =>
    if hasEcPkCollisionAuth P a.2.2 then $ᵗ Bool else contAuth S P a

noncomputable def authExpG1WithProvFrozen1Key (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen1Key prov S P A >>= fun a =>
    if hasEcPkCollisionAuth P a.2.2 || hasBadSigAuth a.2.2 then $ᵗ Bool else contAuth S P a

noncomputable def authExpG2_1WithProvFrozen1Key (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  runAuthWithProvFrozen1Key prov S P A >>= fun a =>
    if (hasEcPkCollisionAuth P a.2.2 || hasBadSigAuth a.2.2) ||
       hasKemPkCollisionAuth a.2.2 then $ᵗ Bool else contAuth S P a

theorem evalDist_pqxdhAuth1KeyExp_eq_G0Frozen1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    𝒟[pqxdhAuth1KeyExp S P A] = 𝒟[authExpG0Frozen1Key S P A] := by
  have hG0 : pqxdhAuth1KeyExp S P A = (do
      let secb ← $ᵗ Bool
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthState S) ProbComp) + pqxdhAuthWithProvImpl1Key S P (checkBundleProvenance P)
      let (b', finalSt) ← (simulateQ impl A.run).run (AuthState.empty S secb)
      contAuth S P (secb, b', finalSt)) := by
    rw [pqxdhAuthWithProvImpl1Key_checkBundleProvenance]
    unfold pqxdhAuth1KeyExp pqxdhAuthExpCoreWith contAuth; simp
  rw [hG0]; unfold authExpG0Frozen1Key runAuthWithProvFrozen1Key; simp only [bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_freeze_hasWonAuth AuthState.hasWonAuth (fun _ => .noneResp)
    (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenance P))
    (pqxdhAuthWithProvImpl1Key_hasWonAuth_sticky S P (checkBundleProvenance P))
    (fun (b', finalSt) => contAuth S P (secb, b', finalSt)) (pure true)
    (fun ⟨b', finalSt⟩ hWon => by dsimp only at hWon; simp [contAuth, hWon])
    A.run (AuthState.empty S secb)

theorem pqxdhAuthWithProvFrozenImpl1Key_commutes_mapAuthSessions (S : Setup) (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool) (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd))
    (q : AuthQuery S) (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    CommutesRel (mapAuthSessions mapEntry) st (pqxdhAuthWithProvFrozenImpl1Key S P prov1 q)
      (pqxdhAuthWithProvFrozenImpl1Key S P prov2 q) := by
  intro mapEntry; unfold pqxdhAuthWithProvFrozenImpl1Key freezeImpl; apply CommutesRel.get_bind
  dsimp only [mapAuthSessions]; apply CommutesRel.ite
  · exact CommutesRel.pure _ st _
  · exact pqxdhAuthWithProvImpl1Key_commutes_mapAuthSessions S P f prov1 prov2 h_prov q st

theorem runAuthWithProvFrozen1Key_eq_map (S : Setup) (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool) (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd)) (A : AuthAdversary S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    runAuthWithProvFrozen1Key prov1 S P A =
      (fun (secb, b', st) => (secb, b', mapAuthSessions mapEntry st)) <$>
        runAuthWithProvFrozen1Key prov2 S P A := by
  intro mapEntry; unfold runAuthWithProvFrozen1Key; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := CommutesRel.simulateQ_add_unif (mapAuthSessions mapEntry)
    (pqxdhAuthWithProvFrozenImpl1Key S P prov1) (pqxdhAuthWithProvFrozenImpl1Key S P prov2)
    (pqxdhAuthWithProvFrozenImpl1Key_commutes_mapAuthSessions S P f prov1 prov2 h_prov)
    A.run (AuthState.empty S secb)
  unfold CommutesRel at hsim; rw [mapAuthSessions_empty] at hsim; rw [hsim, bind_map_left]; rfl

theorem authExpG0_1WithProvFrozen1Key_eq_of_squash (S : Setup) (P : Primitives)
    (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = squashTriples (prov2 p b o bnd))
    (A : AuthAdversary S) :
    authExpG0_1WithProvFrozen1Key prov1 S P A = authExpG0_1WithProvFrozen1Key prov2 S P A := by
  unfold authExpG0_1WithProvFrozen1Key
  rw [runAuthWithProvFrozen1Key_eq_map S P squashTriples prov1 prov2 h_prov A, bind_map_left]
  congr 1; ext ⟨secb, b', st⟩; dsimp only
  rw [hasEcPkCollisionAuth_mapAuthSessions P squashTriples st,
      contAuth_mapAuthSessions_squash S P secb b' st]

theorem authExpG0_1WithProvFrozen1Key_orig_eq_dual (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A =
      authExpG0_1WithProvFrozen1Key (checkBundleProvenanceDual P) S P A := by
  rw [← authExpG0_1WithProvFrozen1Key_eq_of_squash S P
        (checkBundleProvenanceSquashed P) (checkBundleProvenance P)
        (checkBundleProvenanceSquashed_eq_squash_orig P) A,
      authExpG0_1WithProvFrozen1Key_eq_of_squash S P
        (checkBundleProvenanceSquashed P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceSquashed_eq_squash_dual P) A]

theorem authExpG1WithProvFrozen1Key_eq_of_eraseOpk (S : Setup) (P : Primitives)
    (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = eraseOpkTriples (prov2 p b o bnd))
    (A : AuthAdversary S) :
    authExpG1WithProvFrozen1Key prov1 S P A = authExpG1WithProvFrozen1Key prov2 S P A := by
  unfold authExpG1WithProvFrozen1Key
  rw [runAuthWithProvFrozen1Key_eq_map S P eraseOpkTriples prov1 prov2 h_prov A, bind_map_left]
  congr 1; ext ⟨secb, b', st⟩; dsimp only
  rw [hasEcPkCollisionAuth_mapAuthSessions P eraseOpkTriples st,
      hasBadSigAuth_mapAuthSessions_eraseOpk st]
  by_cases h_bad : (hasEcPkCollisionAuth P st || hasBadSigAuth st) = true
  · simp [h_bad]
  · have h_ok : hasBadSigAuth st = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h_bad; exact h_bad.2
    simp [h_bad, contAuth_mapAuthSessions_eraseOpk_of_not_badSig S P secb b' st h_ok]

theorem authExpG1WithProvFrozen1Key_dual_eq_exact (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    authExpG1WithProvFrozen1Key (checkBundleProvenanceDual P) S P A =
      authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A := by
  rw [← authExpG1WithProvFrozen1Key_eq_of_eraseOpk S P
        (checkBundleProvenanceNoOpk P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_dual P) A,
      authExpG1WithProvFrozen1Key_eq_of_eraseOpk S P
        (checkBundleProvenanceNoOpk P) (checkBundleProvenanceExact P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_exact P) A]

end Proofs.SignalPqxdh.Security
