/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-Key `GapDhWithSign` Coupling for Case B

**Checked by Lean.** Proves the per-slot `GapDhWithSign` bound for Case B (`DH2 = CDH(ek_U*, ik_V*)`)
by embedding the challenge identity key with signing access into responder slot `kIdx` and coupling
with a ghost two-key `FgSimInvDh2` state.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik

namespace Proofs.SignalPqxdh.Security.FgGapDh1Key

theorem pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin {S : Setup}
    (sIdx kIdx : ℕ) (ikSk ekSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P q =
      pqxdhKeyIndFgPreImplIk sIdx kIdx (some ekSk) (some ikSk) S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ => rfl

theorem pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin {S : Setup}
    (sIdx kIdx : ℕ) (ikSk ekSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndFgPreImplIk sIdx kIdx (some ekSk) (some ikSk) S P q =
      pqxdhKeyIndFgPreImpl false sIdx (FgGapDh.Ik.noSpkIdx S) (some ekSk) none S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ => rfl

theorem pqxdhKeyIndFgPreImpl1KeyIk_preserves_deadDh2 {S : Setup} (P : Primitives)
    (sIdx kIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (ikSk ekSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst = true) :
    ∀ x ∈ support
      ((pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P q).run hst),
      deadDh2 P sIdx kIdx (P.x25519Base ikSk) x.2 = true := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · intro x hx
    unfold pqxdhKeyIndFgPreImpl1KeyIk fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨sk, hSk, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      let entry1 : PrincipalEntry := {
        secIKA0 := sk, ikAPk := P.x25519Base sk,
        secIKAsign := sk, ikSignPk := P.x25519Base sk, corrupted := false }
      have hPrinX : x.2.base.principals = (u.val, entry1) :: hst.base.principals := by rw [hB]
      have hSessX : x.2.base.sessions = hst.base.sessions := by rw [hB]
      have hTgt : (u.val == kIdx) = true →
          entry1.ikAPk = P.x25519Base ikSk ∧ entry1.corrupted = false := by
        intro hU
        simp only [hU, Bool.true_and, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hSk
        subst hSk
        exact ⟨rfl, rfl⟩
      rw [deadDh2_prin_cons_eq P sIdx kIdx (P.x25519Base ikSk) (hst1 := hst) (hst2 := x.2)
        u.val entry1 hPrinX hSessX hAny hTgt]
      exact hDead
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ (hst1 := hst) (hst2 := x.2)
        (by rw [hB]) (by rw [hB])]
      exact hDead
  · rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin sIdx kIdx ikSk ekSk P q hNe]
    exact pqxdhKeyIndFgPreImplIk_preserves_deadDh2 P sIdx kIdx hsIdx ekSk ikSk q hst hDead

/-- One-key Case B simulation invariant coupling `st.sim` with a ghost two-key `FgSimInvDh2` state
    via `clearTargetSecIKAsign`. -/
def FgSimInvDh2_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (ikSk ekSk : Bytes) (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S) : Prop :=
  ∃ stGhost : FgKeyIndSimState S,
    st.sim = clearTargetSecIKAsign kIdx stGhost ∧
    FgSimInvDh2 S b P hP sIdx kIdx ekSk ikSk hekSk hikSk rem hst stGhost ∧
    2 * min S.N_spk_tot S.N_recv ≤
      (bundleSignedMessages kIdx hst.base.spkBundles).length + 2 * st.sigBudget ∧
    (∀ kv ∈ hst.base.principals, kv.2.secIKAsign = kv.2.secIKA0)

theorem fgSimInvDh2_1Key_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (ikSk ekSk : Bytes) (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32) (secb : Bool) :
    FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyInd1KeySimState.empty S secb) :=
  ⟨_root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb, rfl,
    fgSimInvDh2_empty S b P hP sIdx kIdx ekSk ikSk hekSk hikSk secb,
    by simp [KeyIndFgCutoffState.empty, FgKeyInd1KeySimState.empty, bundleSignedMessages],
    fun _ h => False.elim (List.not_mem_nil h)⟩

theorem fgSimInvDh2_1Key_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen sIdx kIdx : ℕ)
    (ikSk ekSk : Bytes) (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32)
    (a : Bool) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst = false)
    (hInv : FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk rem hst st) :
    𝒟[(pure (badKeyIndFgDh2At P maxLen sIdx kIdx hst.base hst.advRoLog) : ProbComp Bool)] {true} ≤
      𝒟[(pure (P.pow8 (pureExtractCdh2FromAdvRoLog P.isValidDhTriple b.q_total
          (P.x25519Base ekSk) (P.x25519Base ikSk) st.sim.advRoLog) ==
        P.pow8 (P.x25519 ikSk (P.x25519Base ekSk))) : ProbComp Bool)] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, _, _⟩
  have hLogEq : st.sim.advRoLog = stGhost.advRoLog := by rw [hSimEq]; rfl
  rw [hLogEq, hP.pow8_x25519_comm ikSk ekSk]
  exact fgSimInvDh2_terminal_le S b P hP maxLen sIdx kIdx ekSk ikSk hekSk hikSk a rem hst stGhost
    hDead hGhostInv

theorem fgStepCoupling_dh2_initPrin_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (ikSk ekSk : Bytes) (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst = false)
    (hInv : FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst' = false →
      FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P (.initPrin u)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple sIdx kIdx S b.q_total
          (P.x25519Base ikSk) (P.x25519Base ekSk) (.initPrin u)).run st >>= k2] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
  rcases hGhostInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinAnyEq : st.sim.base.principals.any (fun (idx, _) => idx == u.val) =
      hst.base.principals.any (fun (idx, _) => idx == u.val) := by
    rw [hSimEq, clearTargetSecIKAsign_base_principals, any_idx_map_clearTargetPrinSecSign,
      hBaseEq]
    dsimp only [eraseStateFgIk]
    rw [any_idx_erasePrincipalsFg]
  unfold pqxdhKeyIndFgPreImpl1KeyIk fgPreInitPrin1Key liftFgBase fgKeyInd1KeySimImplIk
    fgKeyInd1KeyStepPureIk fgInitPrin1KeyPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and,
    hPrinAnyEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hTgt : (u.val == kIdx) = true
    · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        evalDist_sampleScalar32_const]
      let entry1 : PrincipalEntry := {
        secIKA0 := ikSk, ikAPk := P.x25519Base ikSk,
        secIKAsign := ikSk, ikSignPk := P.x25519Base ikSk, corrupted := false }
      let entryGhost : PrincipalEntry := {
        secIKA0 := [], ikAPk := P.x25519Base ikSk,
        secIKAsign := ikSk, ikSignPk := P.x25519Base ikSk, corrupted := false }
      let stGhost' : FgKeyIndSimState S :=
        { stGhost with base :=
          { stGhost.base with principals := (u.val, entryGhost) :: stGhost.base.principals } }
      have hTgtV' : prinTargetIsV kIdx (P.x25519Base ikSk)
          { hst with base :=
            { hst.base with principals := (u.val, entry1) :: hst.base.principals } } = true := by
        unfold prinTargetIsV at hTgtV ⊢
        simp [List.all_cons, entry1, hTgtV]
      apply hCont (.initPrinResp (P.x25519Base ikSk) (P.x25519Base ikSk))
      · refine Eq.trans ?_ hDead
        exact deadDh2_prin_cons_eq P sIdx kIdx _ (hst1 := hst) u.val entry1 rfl rfl hAny
          (fun _ => ⟨rfl, rfl⟩)
      · refine ⟨stGhost', ?_, ?_, hBudget, ?_⟩
        · dsimp only [stGhost', entryGhost]
          rw [hSimEq]
          simp [clearTargetSecIKAsign, clearTargetSecIKAsignBase,
            clearTargetPrinSecSign, beq_iff_eq.mp hTgt]
        · refine ⟨?_, hAdvEq, hCache, by dsimp [stGhost']; omega, by dsimp; omega, ?_, hTgtV', ?_,
            hSpks, hOpks, hSess⟩
          · dsimp only [stGhost', entry1, entryGhost]
            rw [hBaseEq]
            simp [eraseStateFgIk, erasePrincipalsFg, erasePrincipalEntryFg,
              beq_iff_eq.mp hTgt]
          · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
              hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hikSk, rfl, fun _ => rfl⟩
            · exact hPrins kv hMem
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · rfl
          · exact hSecEq kv hMem
    · have hTgtF : (u.val == kIdx) = false := Bool.eq_false_iff.mpr hTgt
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun sk hSk => ?_)
      have hLen0 : sk.length = 32 := length_of_mem_support_sampleScalar32 hSk
      let entry1 : PrincipalEntry := {
        secIKA0 := sk, ikAPk := P.x25519Base sk,
        secIKAsign := sk, ikSignPk := P.x25519Base sk, corrupted := false }
      let stGhost' : FgKeyIndSimState S :=
        { stGhost with base :=
          { stGhost.base with principals := (u.val, entry1) :: stGhost.base.principals } }
      have hTgtV' : prinTargetIsV kIdx (P.x25519Base ikSk)
          { hst with base :=
            { hst.base with principals := (u.val, entry1) :: hst.base.principals } } = true := by
        unfold prinTargetIsV at hTgtV ⊢
        simp [List.all_cons, hTgtF, hTgtV]
      apply hCont (.initPrinResp (P.x25519Base sk) (P.x25519Base sk))
      · refine Eq.trans ?_ hDead
        exact deadDh2_prin_cons_eq P sIdx kIdx _ (hst1 := hst) u.val entry1 rfl rfl hAny
          (fun h => by rw [hTgtF] at h; cases h)
      · refine ⟨stGhost', ?_, ?_, hBudget, ?_⟩
        · dsimp only [stGhost', entry1]
          rw [hSimEq]
          simp [clearTargetSecIKAsign, clearTargetSecIKAsignBase,
            clearTargetPrinSecSign, beq_eq_false_iff_ne.mp hTgtF]
        · refine ⟨?_, hAdvEq, hCache, by dsimp [stGhost']; omega, by dsimp; omega, ?_, hTgtV', ?_,
            hSpks, hOpks, hSess⟩
          · dsimp only [stGhost', entry1]
            rw [hBaseEq]
            simp [eraseStateFgIk, erasePrincipalsFg, erasePrincipalEntryFg,
              beq_eq_false_iff_ne.mp hTgtF]
          · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
              hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hLen0, rfl, fun h => by rw [hTgtF] at h; cases h⟩
            · exact hPrins kv hMem
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · rfl
          · exact hSecEq kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact hCont .noneResp hst st hDead
      ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hTgtV, hPrins,
        hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩

theorem fgStepCoupling_dh2_corruptIK_tgt_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (ikSk ekSk : Bytes) (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32)
    (u : Fin S.N_id) (hTgt : (u.val == kIdx) = true)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst = false)
    (hInv : FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst' = false →
      FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P (.corruptIK u)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple sIdx kIdx S b.q_total
          (P.x25519Base ikSk) (P.x25519Base ekSk) (.corruptIK u)).run st >>= k2] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
  rcases hGhostInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinFind : st.sim.base.principals.find? (fun (idx, _) => idx == u.val) =
      ((hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg kIdx idx e))).map
        (fun (idx, e) => (idx, clearTargetPrinSecSign kIdx idx e)) := by
    rw [hSimEq, clearTargetSecIKAsign_base_principals, find?_idx_map_clearTargetPrinSecSign,
      hBaseEq]
    dsimp only [eraseStateFgIk]
    rw [find?_idx_erasePrincipalsFg]
  unfold pqxdhKeyIndFgPreImpl1KeyIk pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl
    liftFgBase fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinFind, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    dsimp only [Option.map]
    simp only [StateT.run_pure, pure_bind]
    exact hCont .noneResp hst st hDead
      ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hTgtV, hPrins,
        hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩
  | some p =>
    rcases p with ⟨u0, entry⟩
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    rw [hDeadCont _ _ (deadDh2_map_corrupted_eq_true_of_eq P sIdx kIdx u.val _ hTgt hst hTgtV u0
      entry hF)]
    exact zero_le

theorem fgStepCoupling_dh2_genSPK_tgt_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (ikSk ekSk : Bytes) (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hTgtPrin : (u.val == kIdx) = true)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst = false)
    (hInv : FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst' = false →
      FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P (.genSPK u j)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple sIdx kIdx S b.q_total
          (P.x25519Base ikSk) (P.x25519Base ekSk) (.genSPK u j)).run st >>= k2] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
  rcases hGhostInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinFind : st.sim.base.principals.find? (fun (idx, _) => idx == u.val) =
      ((hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg kIdx idx e))).map
        (fun (idx, e) => (idx, clearTargetPrinSecSign kIdx idx e)) := by
    rw [hSimEq, clearTargetSecIKAsign_base_principals, find?_idx_map_clearTargetPrinSecSign,
      hBaseEq]
    dsimp only [eraseStateFgIk]
    rw [find?_idx_erasePrincipalsFg]
  have hSpkEq : st.sim.base.spkBundles = hst.base.spkBundles := by
    rw [hSimEq, clearTargetSecIKAsign_base_spkBundles, hBaseEq]; rfl
  have hTgtSpkF : (FgGapDh.spkBundleFlatIdx S u j == FgGapDh.Ik.noSpkIdx S) = false :=
    spkBundleFlatIdx_ne_noSpkIdx S u j
  unfold pqxdhKeyIndFgPreImpl1KeyIk pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
    fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk fgGenSPK1KeyPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and, hTgtPrin, ↓reduceIte,
    hSpkEq, hPrinFind, bind_assoc, pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact hCont .noneResp hst st hDead
        ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hTgtV, hPrins,
          hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩
    | some p =>
      rcases p with ⟨u0, uEntry⟩
      dsimp only [Option.map]
      simp only [clearTargetPrinSecSign_ikAPk, erasePrincipalEntryFg_ikAPk]
      let dummyB : SpkBundleEntry :=
        { spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
      have huEq : u.val = kIdx := beq_iff_eq.mp hTgtPrin
      have hLenPlus2 :
          (bundleSignedMessages kIdx hst.base.spkBundles).length + 2 ≤
            2 * min S.N_spk_tot S.N_recv := by
        rw [← huEq]
        exact bundleSignedMessages_length_add_two_le S u j dummyB hst.base.spkBundles
          hValidEc.2.1 hAny
      have hBudZeroF : (st.sigBudget == 0) = false := by
        cases hEq0 : (st.sigBudget == 0)
        · rfl
        · have := beq_iff_eq.mp hEq0; omega
      have huMem : (u0, uEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
      have hu0Eq : u0 = u.val :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFP)
      have hu0Tgt : (u0 == kIdx) = true := by rw [hu0Eq]; exact hTgtPrin
      have hSignEq : uEntry.secIKAsign = ikSk := by
        rw [hSecEq (u0, uEntry) huMem, (hPrins (u0, uEntry) huMem).2.2 hu0Tgt]
      simp only [hBudZeroF, hTgtSpkF, Bool.false_eq_true, ↓reduceIte, hSignEq,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
        sampleKemKeyGen, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun spkSk hSpk => ?_)
      have hSpkLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpk
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
      let spkPk := P.x25519Base spkSk
      let pqspkPk := (P.kemKeyGen seedKem).1
      let pqspkSk := (P.kemKeyGen seedKem).2
      let bEntry1 : SpkBundleEntry := {
        spkSk := spkSk, spkPk := spkPk,
        spkSig := P.sigSign ikSk (encodeEC spkPk) rSpk,
        pqspkSk := pqspkSk, pqspkPk := pqspkPk,
        pqspkSig := P.sigSign ikSk (encodeKEM pqspkPk) rPq }
      let bundleOut : PreKeyBundleInput := {
        ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
        spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
        pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
      let hst' : KeyIndFgCutoffState S :=
        { hst with base :=
          { hst.base with spkBundles := ((u.val, j.val), bEntry1) :: hst.base.spkBundles } }
      let stGhost' : FgKeyIndSimState S :=
        { stGhost with base :=
          { stGhost.base with spkBundles := ((u.val, j.val), bEntry1) :: stGhost.base.spkBundles } }
      have hDead' : deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst' = false := by
        rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ (hst1 := hst) (hst2 := hst') rfl rfl]
        exact hDead
      have hInvGhost' : FgSimInvDh2 S b P hP sIdx kIdx ekSk ikSk hekSk hikSk rem hst' stGhost' := by
        refine ⟨?_, hAdvEq, hCache, by dsimp [stGhost']; omega, by dsimp [hst']; omega,
          ⟨hValidEc.1,
            (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
            hValidEc.2.2.1, hValidEc.2.2.2⟩,
          hTgtV, hPrins, ?_, hOpks, hSess⟩
        · dsimp only [stGhost', hst', bEntry1]
          rw [hBaseEq]; rfl
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hSpkLen, rfl⟩
          · exact hSpks kv hMem
      refine hCont (.bundleResp bundleOut) hst' _ hDead'
        ⟨stGhost', ?_, hInvGhost', ?_, hSecEq⟩
      · dsimp only [stGhost', bEntry1, spkPk, pqspkPk, pqspkSk, Primitives.kemKeyGen]
        rw [hSimEq]
        dsimp only [clearTargetSecIKAsign, clearTargetSecIKAsignBase]
        rw [hBaseEq]
        rfl
      · dsimp only [hst']
        rw [huEq, bundleSignedMessages_cons_eq, List.length_cons, List.length_cons]
        omega
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact hCont .noneResp hst st hDead
      ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hTgtV, hPrins,
        hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩

theorem fgKeyInd1KeySimImplIk_run_delegated {S : Setup} (P : Primitives) (ikSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (sIdx kIdx maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (hq : isDelegatedQuery1Key kIdx q = true)
    (hNeInit : ∀ u, q ≠ .initPrin u)
    (st : FgKeyInd1KeySimState S) (stGhost : FgKeyIndSimState S)
    (hSimEq : st.sim = clearTargetSecIKAsign kIdx stGhost) :
    (fgKeyInd1KeySimImplIk P ikSk ddh sIdx kIdx S maxLen U V q).run st =
      ((fgKeyIndSimImplIk P ddh sIdx kIdx S maxLen V U q).run stGhost >>=
        fun p => pure (p.1, { st with sim := clearTargetSecIKAsign kIdx p.2 })) := by
  have hStep : (fgKeyInd1KeySimImplIk P ikSk ddh sIdx kIdx S maxLen U V q).run st =
      (fgKeyIndStepPure P ddh false sIdx (FgGapDh.Ik.noSpkIdx S) S maxLen V U q st.sim >>=
        fun p => pure (p.1, { st with sim := p.2 })) := by
    cases q with
    | initPrin _ => cases hq
    | genSPK u j =>
      have hNe : (u.val == kIdx) = false := by
        simpa [isDelegatedQuery1Key] using hq
      unfold fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk fgGenSPK1KeyPure
      simp [hNe]
    | _ =>
      unfold fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk
      rfl
  have hRhs : (fgKeyIndSimImplIk P ddh sIdx kIdx S maxLen V U q).run stGhost =
      fgKeyIndStepPure P ddh false sIdx (FgGapDh.Ik.noSpkIdx S) S maxLen V U q stGhost := by
    rw [fgKeyIndSimImplIk_run]
    cases q with
    | initPrin u => exact absurd rfl (hNeInit u)
    | _ => rfl
  rw [hStep, hRhs, hSimEq,
    fgKeyIndStepPure_clearTargetSecIKAsign_delegated P ddh false sIdx (FgGapDh.Ik.noSpkIdx S) kIdx
      S maxLen V U q hq stGhost]
  simp only [bind_assoc, pure_bind]

theorem fgStepCoupling_dh2_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (ikSk ekSk : Bytes) (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst = false)
    (hInv : FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst' = false →
      FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh2 P sIdx kIdx (P.x25519Base ikSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P q).run hst >>= k1] {true}
      ≤
      𝒟[(fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple sIdx kIdx S b.q_total
          (P.x25519Base ikSk) (P.x25519Base ekSk) q).run st >>= k2] {true} := by
  have hCases :
      (∃ u, q = .initPrin u) ∨
      (∃ u, q = .corruptIK u ∧ (u.val == kIdx) = true) ∨
      (∃ u j, q = .genSPK u j ∧ (u.val == kIdx) = true) ∨
      (isDelegatedQuery1Key kIdx q = true ∧ ∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | corruptIK u =>
      by_cases h : (u.val == kIdx) = true
      · exact Or.inr (Or.inl ⟨u, rfl, h⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [isDelegatedQuery1Key, h], fun _ hc => by cases hc⟩))
    | genSPK u j =>
      by_cases h : (u.val == kIdx) = true
      · exact Or.inr (Or.inr (Or.inl ⟨u, j, rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [isDelegatedQuery1Key, h], fun _ hc => by cases hc⟩))
    | _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, fun _ hc => by cases hc⟩))
  rcases hCases with ⟨u, rfl⟩ | ⟨u, rfl, hTgt⟩ | ⟨u, j, rfl, hTgt⟩ | ⟨hDel, hNeInit⟩
  · exact fgStepCoupling_dh2_initPrin_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk u rem hst st
      hDead hInv k1 k2 hCont
  · exact fgStepCoupling_dh2_corruptIK_tgt_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk u hTgt rem
      hst st hDead hInv k1 k2 hCont hDeadCont
  · exact fgStepCoupling_dh2_genSPK_tgt_1Key S b P hP sIdx kIdx ikSk ekSk hikSk hekSk u j hTgt rem
      hst st hDead hInv k1 k2 hCont
  · rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
    rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin sIdx kIdx ikSk ekSk P q hNeInit,
      fgKeyInd1KeySimImplIk_run_delegated P ikSk P.isValidDhTriple sIdx kIdx b.q_total
        (P.x25519Base ikSk) (P.x25519Base ekSk) q hDel hNeInit st stGhost hSimEq]
    simp only [bind_assoc, pure_bind]
    let k1' : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool :=
      open scoped Classical in
      fun p => if PreStepPreserves1KeyAux hst p.2 then k1 p else pure false
    have hLhsEq :
        𝒟[(pqxdhKeyIndFgPreImplIk sIdx kIdx (some ekSk) (some ikSk) S P q).run hst >>= k1] =
        𝒟[(pqxdhKeyIndFgPreImplIk sIdx kIdx (some ekSk) (some ikSk) S P q).run hst >>= k1'] := by
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
      rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin sIdx kIdx ikSk ekSk P q hNeInit]
        at hx
      have hAux := pqxdhKeyIndFgPreImpl_preserves_1KeyAux_of_ne_initPrin false sIdx
        (FgGapDh.Ik.noSpkIdx S) (some ekSk) none P q hNeInit hst x hx
      simp only [k1', hAux, ↓reduceIte]
    rw [hLhsEq]
    refine fgStepCoupling_dh2 S b P hP sIdx kIdx ekSk ikSk hekSk hikSk q rem hst stGhost hDead
      hGhostInv k1' (fun p => k2 (p.1, { st with sim := clearTargetSecIKAsign kIdx p.2 }))
      (fun r hst' stGhost' hD' hGInv' => ?_) (fun r hst' hD' => ?_)
    · dsimp only [k1']
      split_ifs with hAux
      · exact hCont r hst' { st with sim := clearTargetSecIKAsign kIdx stGhost' } hD'
          ⟨stGhost', rfl, hGInv', by dsimp only; have := hAux.2 kIdx; omega, hAux.1 hSecEq⟩
      · simp
    · dsimp only [k1']
      split_ifs with hAux
      · exact hDeadCont r hst' hD'
      · simp

/-- Per-slot Case B (`DH2`) bound on `badKeyIndFgDh2At` in `runKeyIndFgSim1Key` against
    `GapDhWithSignReal`. -/
theorem prob_badKeyIndFgDh2At_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (kIdx : ℕ) (_hkIdx : kIdx ∈ Finset.range S.N_id) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhAdvAtIk sIdx kIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_dh2 sIdx kIdx P A.1
    (fun x => pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhAdvAtIk_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ikSk hikSk => ?_)
  have hikLen : ikSk.length = 32 := length_of_mem_support_sampleScalar32 hikSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ekSk hekSk => ?_)
  have hekLen : ekSk.length = 32 := length_of_mem_support_sampleScalar32 hekSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh2 P sIdx kIdx (P.x25519Base ikSk))
    (FgSimInvDh2_1Key S b P hP sIdx kIdx ikSk ekSk hikLen hekLen)
    (pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P)
    (fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple sIdx kIdx S b.q_total (P.x25519Base ikSk)
      (P.x25519Base ekSk))
    (fun q s1 hD x hx =>
      pqxdhKeyIndFgPreImpl1KeyIk_preserves_deadDh2 P sIdx kIdx hsLt ikSk ekSk q s1 hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh2_1Key S b P hP sIdx kIdx ikSk ekSk hikLen hekLen q rem s1 s2 hDF hInv k1 k2
        hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdh2FromAdvRoLog P.isValidDhTriple b.q_total
        (P.x25519Base ekSk) (P.x25519Base ikSk) x.2.sim.advRoLog) ==
      P.pow8 (P.x25519 ikSk (P.x25519Base ekSk))))
    (fun a s1 hD =>
      by simp [badKeyIndFgDh2At_eq_false_of_deadDh2 P b.q_ro sIdx kIdx (P.x25519Base ikSk) s1 hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh2_1Key_terminal_le S b P hP b.q_ro sIdx kIdx ikSk ekSk hikLen hekLen a rem s1 s2
        hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeySimState.empty S secb)
    (fgSimInvDh2_1Key_empty S b P hP sIdx kIdx ikSk ekSk hikLen hekLen secb)

end Proofs.SignalPqxdh.Security.FgGapDh1Key
