/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyPre
import VCVio.EvalDist.Monad.Basic

/-!
# One-Key `GapDhWithSign` Coupling for Cases C and D

**Checked by Lean.** Proves the per-slot `GapDhWithSign` bounds for Cases C (`DH3 = CDH(ek_U*, spk_V*)`)
and D (`DH4 = CDH(ek_U*, opk_V*)`), sampling all identity scalars locally with zero signing queries
and delegating non-identity steps to the two-key coupling lemmas.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security.FgGapDh1Key

/-! ## Case C (`DH3`) -/

theorem spkTargetRevealed_eq_of_spkBundles_eq {S : Setup} (bIdx : ℕ)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hSpk : hst2.base.spkBundles = hst1.base.spkBundles) :
    spkTargetRevealed bIdx hst2 = spkTargetRevealed bIdx hst1 := by
  unfold spkTargetRevealed
  have hFiredIff : hasFiredSpk S bIdx hst2 ↔ hasFiredSpk S bIdx hst1 := by
    unfold hasFiredSpk
    rw [hSpk]
  have hDecEq :
      @decide (hasFiredSpk S bIdx hst2) (Classical.propDecidable _) =
      @decide (hasFiredSpk S bIdx hst1) (Classical.propDecidable _) := by
    by_cases h1 : hasFiredSpk S bIdx hst1
    · rw [@decide_eq_true _ (Classical.propDecidable _) (hFiredIff.mpr h1),
        @decide_eq_true _ (Classical.propDecidable _) h1]
    · rw [@decide_eq_false _ (Classical.propDecidable _) (fun h2 => h1 (hFiredIff.mp h2)),
        @decide_eq_false _ (Classical.propDecidable _) h1]
  rw [hDecEq, hSpk]

theorem deadDh3Full_eq_of_spk_sess {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hSpk : hst2.base.spkBundles = hst1.base.spkBundles)
    (hSess : (hst2.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerSpkPk =
      (hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerSpkPk) :
    deadDh3Full P sIdx bIdx V hst2 = deadDh3Full P sIdx bIdx V hst1 := by
  unfold deadDh3Full
  rw [deadDh3_eq_of_spk_sess P sIdx bIdx V hSpk hSess,
    spkTargetRevealed_eq_of_spkBundles_eq bIdx hSpk]

theorem pqxdhKeyIndFgPreImpl1Key_preserves_deadDh3Full {S : Setup} (P : Primitives)
    (sIdx bIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl1Key false sIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadDh3Full P sIdx bIdx (P.x25519Base vSk) x.2 = true := by
  cases q
  case initPrin u =>
    intro x hx
    unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      rw [deadDh3Full_eq_of_spk_sess P sIdx bIdx _ (hst1 := hst) (hst2 := x.2)
        (by rw [hB]) (by rw [hB])]
      exact hDead
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq
      have hB := (Prod.mk.inj hEq).2
      rw [deadDh3Full_eq_of_spk_sess P sIdx bIdx _ (hst1 := hst) (hst2 := x.2)
        (by rw [hB]) (by rw [hB])]
      exact hDead
  all_goals
    exact pqxdhKeyIndFgPreImpl_preserves_deadDh3Full P sIdx bIdx hsIdx uSk vSk _ hst hDead

def FgSimInvDh3_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S) : Prop :=
  FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st.sim

theorem fgSimInvDh3_1Key_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (secb : Bool) :
    FgSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyInd1KeySimState.empty S secb) :=
  fgSimInvDh3_empty S b P hP sIdx bIdx uSk vSk huSk hvSk secb

theorem fgStepCoupling_dh3_initPrin_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDeadFull : deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl1Key false sIdx bIdx (some uSk) (some vSk) S P (.initPrin u)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImpl P uSk P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u)).run st >>= k2] {true} := by
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinEq : st.sim.base.principals = hst.base.principals := by
    rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key liftFgBase fgKeyInd1KeySimImpl
    fgKeyInd1KeyStepPure fgInitPrin1KeyPure
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
    apply hContFull (.initPrinResp entry.ikAPk entry.ikSignPk)
    · rw [deadDh3Full_eq_of_spk_sess P sIdx bIdx _ rfl rfl]
      exact hDeadFull
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache,
        by dsimp; omega, by dsimp; omega, ?_, hSpkV, ?_, hSpks, hOpks, hSess⟩
      · exact ⟨(validPrincipals_cons S u entry hst.base.principals hValidEc.1 hAny).1,
          hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen0, rfl⟩
        · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact hContFull .noneResp hst st hDeadFull
      ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩

theorem pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin {S : Setup} (useDh1 : Bool)
    (sIdx bIdx : ℕ) (optU optV : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndFgPreImpl1Key useDh1 sIdx bIdx optU optV S P q =
      pqxdhKeyIndFgPreImpl useDh1 sIdx bIdx optU optV S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ => rfl

theorem fgKeyInd1KeySimImpl_false_run_of_ne_initPrin {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (sIdx bIdx maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) (st : FgKeyInd1KeySimState S) :
    (fgKeyInd1KeySimImpl P uSk ddh false sIdx bIdx S maxLen U V q).run st =
      ((fgKeyIndSimImpl P ddh false sIdx bIdx S maxLen U V q).run st.sim >>=
        fun p => pure (p.1, { st with sim := p.2 })) := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | genSPK u j =>
    unfold fgKeyInd1KeySimImpl fgKeyInd1KeyStepPure fgGenSPK1KeyPure fgKeyIndSimImpl
    simp
  | _ =>
    unfold fgKeyInd1KeySimImpl fgKeyInd1KeyStepPure fgKeyIndSimImpl
    simp

theorem fgStepCoupling_dh3_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDeadFull : deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadContFull : ∀ r hst', deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1Key false sIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true}
      ≤
      𝒟[(fgKeyInd1KeySimImpl P uSk P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact fgStepCoupling_dh3_initPrin_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk u rem hst st
      hDeadFull hInv k1 k2 hContFull
  · rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin false sIdx bIdx (some uSk) (some vSk) P q hNe,
      fgKeyInd1KeySimImpl_false_run_of_ne_initPrin P uSk P.isValidDhTriple sIdx bIdx b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q hNe st]
    simp only [bind_assoc, pure_bind]
    exact fgStepCoupling_dh3 S b P hP sIdx bIdx uSk vSk huSk hvSk q rem hst st.sim hDeadFull hInv
      k1 (fun p => k2 (p.1, { st with sim := p.2 }))
      (fun r hst' sim' hDF' hInv' =>
        hContFull r hst' { st with sim := sim' } hDF' hInv')
      hDeadContFull

/-- Per-slot Case C (`DH3`) bound on `badKeyIndFgDh3At` in `runKeyIndFgSim1Key` against
    `GapDhWithSignReal`. -/
theorem prob_badKeyIndFgDh3At_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (bIdx : ℕ) (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhAdvAt false sIdx bIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_dh3 sIdx bIdx P A.1
    (fun x => pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh3Full P sIdx bIdx (P.x25519Base vSk))
    (FgSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huLen hvLen)
    (pqxdhKeyIndFgPreImpl1Key false sIdx bIdx (some uSk) (some vSk) S P)
    (fgKeyInd1KeySimImpl P uSk P.isValidDhTriple false sIdx bIdx S b.q_total (P.x25519Base uSk)
      (P.x25519Base vSk))
    (fun q s1 hD x hx =>
      pqxdhKeyIndFgPreImpl1Key_preserves_deadDh3Full P sIdx bIdx hsLt uSk vSk q s1 hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh3_1Key S b P hP sIdx bIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2
        hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdhFromAdvRoLog P.isValidDhTriple false b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.sim.advRoLog) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD =>
      by simp [badKeyIndFgDh3At_eq_false_of_deadDh3Full P b.q_ro sIdx bIdx (P.x25519Base vSk) s1
        hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh3_terminal_le S b P hP b.q_ro sIdx bIdx uSk vSk huLen hvLen a rem s1 s2.sim
        hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeySimState.empty S secb)
    (fgSimInvDh3_1Key_empty S b P hP sIdx bIdx uSk vSk huLen hvLen secb)

/-! ## Case D (`DH4`) -/

theorem pqxdhKeyIndFgPreImpl1KeyOpk_preserves_deadDh4 {S : Setup} (P : Primitives)
    (sIdx oIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl1KeyOpk sIdx oIdx (some uSk) (some vSk) S P q).run hst),
      deadDh4 P sIdx oIdx (P.x25519Base vSk) x.2 = true := by
  cases q
  case initPrin u =>
    intro x hx
    unfold pqxdhKeyIndFgPreImpl1KeyOpk fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ (hst1 := hst) (hst2 := x.2)
        (by rw [hB]) (by rw [hB])]
      exact hDead
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq
      have hB := (Prod.mk.inj hEq).2
      rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ (hst1 := hst) (hst2 := x.2)
        (by rw [hB]) (by rw [hB])]
      exact hDead
  all_goals
    exact pqxdhKeyIndFgPreImplOpk_preserves_deadDh4 P sIdx oIdx hsIdx uSk vSk _ hst hDead

def FgSimInvDh4_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S) : Prop :=
  FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st.sim

theorem fgSimInvDh4_1Key_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (secb : Bool) :
    FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyInd1KeySimState.empty S secb) :=
  fgSimInvDh4_empty S b P hP sIdx oIdx uSk vSk huSk hvSk secb

theorem fgStepCoupling_dh4_initPrin_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyOpk sIdx oIdx (some uSk) (some vSk) S P (.initPrin u)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImplOpk P uSk P.isValidDhTriple sIdx oIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u)).run st >>= k2] {true} := by
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinEq : st.sim.base.principals = hst.base.principals := by
    rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl1KeyOpk fgPreInitPrin1Key liftFgBase fgKeyInd1KeySimImplOpk
    fgKeyInd1KeyStepPureOpk fgInitPrin1KeyPure
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
    · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]
      exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache,
        by dsimp; omega, by dsimp; omega, ?_, hOpkV, ?_, hSpks, hOpks, hSess⟩
      · exact ⟨(validPrincipals_cons S u entry hst.base.principals hValidEc.1 hAny).1,
          hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen0, rfl⟩
        · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact hCont .noneResp hst st hDead
      ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hOpkV, hPrins, hSpks, hOpks, hSess⟩

theorem pqxdhKeyIndFgPreImpl1KeyOpk_eq_of_ne_initPrin {S : Setup}
    (sIdx oIdx : ℕ) (optU optV : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndFgPreImpl1KeyOpk sIdx oIdx optU optV S P q =
      pqxdhKeyIndFgPreImplOpk sIdx oIdx optU optV S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ => rfl

theorem fgKeyInd1KeySimImplOpk_run_of_ne_initPrin {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (sIdx oIdx maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) (st : FgKeyInd1KeySimState S) :
    (fgKeyInd1KeySimImplOpk P uSk ddh sIdx oIdx S maxLen U V q).run st =
      ((fgKeyIndSimImplOpk P ddh sIdx oIdx S maxLen U V q).run st.sim >>=
        fun p => pure (p.1, { st with sim := p.2 })) := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | genSPK u j =>
    rw [fgKeyIndSimImplOpk_run]
    unfold fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk fgGenSPK1KeyPure fgKeyIndStepPureOpk
    simp
  | _ =>
    rw [fgKeyIndSimImplOpk_run]
    unfold fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk
    simp

theorem fgStepCoupling_dh4_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyOpk sIdx oIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true}
      ≤
      𝒟[(fgKeyInd1KeySimImplOpk P uSk P.isValidDhTriple sIdx oIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact fgStepCoupling_dh4_initPrin_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk u rem hst st
      hDead hInv k1 k2 hCont
  · rw [pqxdhKeyIndFgPreImpl1KeyOpk_eq_of_ne_initPrin sIdx oIdx (some uSk) (some vSk) P q hNe,
      fgKeyInd1KeySimImplOpk_run_of_ne_initPrin P uSk P.isValidDhTriple sIdx oIdx b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q hNe st]
    simp only [bind_assoc, pure_bind]
    exact fgStepCoupling_dh4 S b P hP sIdx oIdx uSk vSk huSk hvSk q rem hst st.sim hDead hInv
      k1 (fun p => k2 (p.1, { st with sim := p.2 }))
      (fun r hst' sim' hD' hInv' =>
        hCont r hst' { st with sim := sim' } hD' hInv')
      hDeadCont

/-- Per-slot Case D (`DH4`) bound on `badKeyIndFgDh4At` in `runKeyIndFgSim1Key` against
    `GapDhWithSignReal`. -/
theorem prob_badKeyIndFgDh4At_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (oIdx : ℕ) (_hoIdx : oIdx ∈ Finset.range S.N_opk_tot) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhAdvAtOpk sIdx oIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_dh4 sIdx oIdx P A.1
    (fun x => pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhAdvAtOpk_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh4 P sIdx oIdx (P.x25519Base vSk))
    (FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huLen hvLen)
    (pqxdhKeyIndFgPreImpl1KeyOpk sIdx oIdx (some uSk) (some vSk) S P)
    (fgKeyInd1KeySimImplOpk P uSk P.isValidDhTriple sIdx oIdx S b.q_total (P.x25519Base uSk)
      (P.x25519Base vSk))
    (fun q s1 hD x hx =>
      pqxdhKeyIndFgPreImpl1KeyOpk_preserves_deadDh4 P sIdx oIdx hsLt uSk vSk q s1 hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh4_1Key S b P hP sIdx oIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2
        hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdh4FromAdvRoLog P.isValidDhTriple b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.sim.advRoLog) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD =>
      by simp [badKeyIndFgDh4At_eq_false_of_deadDh4 P b.q_ro sIdx oIdx (P.x25519Base vSk) s1 hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh4_terminal_le S b P hP b.q_ro sIdx oIdx uSk vSk huLen hvLen a rem s1 s2.sim
        hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeySimState.empty S secb)
    (fgSimInvDh4_1Key_empty S b P hP sIdx oIdx uSk vSk huLen hvLen secb)

end Proofs.SignalPqxdh.Security.FgGapDh1Key
