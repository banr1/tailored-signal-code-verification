/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhRestDh3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdPre
import VCVio.EvalDist.Monad.Basic

/-!
# One-key `Auth` Case C (`DH3`) `GapDhWithSign` bound

**Checked by Lean.** Bounds the per-index Case C (`DH3`) bad event of `runAuthFgLatchedSim1Key` by
the `GapDhWithSign` advantage of `fgAuth1KeyGapDhAdvAt false sIdx bIdx`, which samples all honest
identity scalars locally with zero signing queries and reuses `AuthDh3.fgAuthStepCoupling_dh3` off
`.initPrin`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-- One-key Case C simulation invariant: `AuthDh3.FgAuthSimInvDh3` on `st.sim`. -/
def FgAuthSimInvDh3_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S) : Prop :=
  AuthDh3.FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st.sim

theorem fgAuthSimInvDh3_1Key_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (secb : Bool) :
    FgAuthSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk b.q_total
      (AuthFgCutoffState.empty S secb) (FgAuth1KeySimState.empty S secb) :=
  AuthDh3.fgAuthSimInvDh3_empty S b P hP sIdx bIdx uSk vSk huSk hvSk secb

theorem fgAuth1KeyStepCoupling_dh3_initPrin (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgAuthSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgAuthSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx (some uSk) (some vSk) S P (.initPrin u)).run hst
      >>= k1] {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u)).run st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hPrinEq : st.sim.base.principals = hst.base.principals := hBaseRel.principals_eq
  unfold pqxdhAuthFgPreImpl1KeyDh3 liftAuthFgBase pqxdhAuthImpl1Key fgAuth1KeySimImpl
    fgAuth1KeyStepHaltPure fgAuth1KeyStepPure fgAuthInitPrin1KeyPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, hPrinEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun sk hSk => ?_)
    have hLen0 : sk.length = 32 := length_of_mem_support_sampleScalar32 hSk
    let entry : PrincipalEntry := {
      secIKA0 := sk, ikAPk := P.x25519Base sk,
      secIKAsign := sk, ikSignPk := P.x25519Base sk, corrupted := false }
    apply hCont (.initPrinResp entry.ikAPk entry.ikSignPk)
    · rw [AuthDh3.deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · refine ⟨⟨hBaseRel.secb_eq, by dsimp [erasePrincipalsOptFg],
        hBaseRel.spkBundles_eq, hBaseRel.opkEntries_eq, hBaseRel.sessions_eq,
        hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq,
        hBaseRel.usedKyberTriples_eq⟩,
        hRespEq, hAdvEq, hCache, hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
        ⟨(validPrincipals_cons S u entry hst.base.principals hValidEc.1 hAny).1, hValidEc.2.1,
          hValidEc.2.2.1, hValidEc.2.2.2⟩,
        hSpkV, ?_, hSpks, hOpks, hSess⟩
      intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
      · exact ⟨hLen0, rfl⟩
      · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact AuthDh3.fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst
      st.sim hDead hInv0 .noneResp k1 (fun p => k2 (p.1, { st with sim := p.2 }))
      (fun r hst' sim' hDF' hInv' => hCont r hst' { st with sim := sim' } hDF' hInv')

theorem fgAuth1KeySimImpl_false_run_of_not_initPrin {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (sIdx bIdx maxLen : ℕ) (U V : Bytes)
    (q : AuthQuery S) (hq : ∀ u, q ≠ .initPrin u) (st : FgAuth1KeySimState S) :
    (fgAuth1KeySimImpl P uSk ddh false sIdx bIdx S maxLen U V q).run st =
      ((fgAuthSimImpl P ddh false sIdx bIdx S maxLen U V q).run st.sim >>=
        fun p => pure (p.1, { st with sim := p.2 })) := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | genSPK u j =>
    unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure fgAuthGenSPK1KeyPure
      fgAuthSimImpl
    simp
  | _ =>
    unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure fgAuthSimImpl
    simp

theorem fgAuth1KeyStepCoupling_dh3 (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgAuthSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgAuthSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true}
      ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact fgAuth1KeyStepCoupling_dh3_initPrin S b P hP sIdx bIdx uSk vSk huSk hvSk u rem hst st
      hDead hInv k1 k2 hCont
  · rw [pqxdhAuthFgPreImpl1KeyDh3_of_not_initPrin sIdx bIdx (some uSk) (some vSk) P q hNe,
      fgAuth1KeySimImpl_false_run_of_not_initPrin P uSk P.isValidDhTriple sIdx bIdx b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q hNe st]
    simp only [bind_assoc, pure_bind]
    exact AuthDh3.fgAuthStepCoupling_dh3 S b P hP sIdx bIdx uSk vSk huSk hvSk q rem hst st.sim
      hDead hInv k1 (fun p => k2 (p.1, { st with sim := p.2 }))
      (fun r hst' sim' hDF' hInv' => hCont r hst' { st with sim := sim' } hDF' hInv')
      hDeadCont

theorem prob_badAuthFgDh3AtCore_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (AuthAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (bIdx : ℕ) (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runAuthFgSim1Key S P A.1 >>= fun x =>
        pure (badAuthFgDh3AtCore P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog
          x.2.2.respRecs)] {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt false sIdx bIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runAuthFgSim1Key_eq_preSample_dh3 sIdx bIdx P hP A.1
    (fun x => pure (badAuthFgDh3AtCore P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog
      x.2.2.respRecs))]
  rw [gapDhWithSignExp_fgAuth1KeyGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.auth_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadAuthDh3 P sIdx bIdx (P.x25519Base vSk))
    (FgAuthSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huLen hvLen)
    (pqxdhAuthFgPreImpl1KeyDh3 sIdx bIdx (some uSk) (some vSk) S P)
    (fgAuth1KeySimImpl P uSk P.isValidDhTriple false sIdx bIdx S b.q_total (P.x25519Base uSk)
      (P.x25519Base vSk))
    (fun q s1 hD x hx =>
      pqxdhAuthFgPreImpl1KeyDh3_preserves_deadAuthDh3 P sIdx bIdx hsLt uSk vSk q s1 hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgAuth1KeyStepCoupling_dh3 S b P hP sIdx bIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2
        hCont hDeadCont)
    (fun x => pure (badAuthFgDh3AtCore P b.q_ro sIdx bIdx x.2.base x.2.advRoLog x.2.respRecs))
    (fun x => pure (P.pow8 (pureExtractCdhFromAuthSimState S P P.isValidDhTriple false b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.sim) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD =>
      by simp [badAuthFgDh3AtCore_eq_false_of_deadAuthDh3 P b.q_ro sIdx bIdx (P.x25519Base vSk) s1
        hD])
    (fun a rem s1 s2 hDF hInv =>
      AuthDh3.fgAuthSimInvDh3_terminal_le S b P hP b.q_ro sIdx bIdx uSk vSk huLen hvLen a rem s1
        s2.sim hDF hInv)
    A.1.run b.q_total hQb
    (AuthFgCutoffState.empty S secb)
    (FgAuth1KeySimState.empty S secb)
    (fgAuthSimInvDh3_1Key_empty S b P hP sIdx bIdx uSk vSk huLen hvLen secb)

/-- Bounds `badAuthFgDh3At` in `runAuthFgLatchedSim1Key` by the `GapDhWithSign` advantage of
`fgAuth1KeyGapDhAdvAt false sIdx bIdx`. -/
theorem prob_badAuthFgDh3At_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (AuthAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (bIdx : ℕ) (hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runAuthFgLatchedSim1Key S P A.1 >>= fun x =>
        pure (badAuthFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog
          x.2.2.respRecs)] {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgAuth1KeyGapDhAdvAt false sIdx bIdx S b A) := by
  rw [evalDist_runAuthFgLatchedSim1Key_badAuthFgDh3At_eq]
  refine le_trans ?_ (prob_badAuthFgDh3AtCore_1Key_le_gapDhWithSign S b P hP A sIdx hsIdx bIdx
    hbIdx)
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  refine evalDist_bind_true_mono_of_support (runAuthFgSim1Key S P A.1) _ _ (fun x _ => ?_)
  by_cases h : badAuthFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog x.2.2.respRecs = true
  · rw [h, badAuthFgDh3At_imp_core P b.q_ro sIdx bIdx _ _ _ h]
  · simp [Bool.eq_false_iff.mpr h]

end Proofs.SignalPqxdh.Security
