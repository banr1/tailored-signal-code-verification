/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpkInv
import VCVio.EvalDist.Monad.Basic

/-!
# Case D (`DH4`) Step Coupling and `GapDH` Bound

Per-query couplings between the pre-sampled game `pqxdhKeyIndFgPreImplOpk` and the `GapDH`
simulator `fgKeyIndSimImplOpk` under `FgSimInvDh4`, yielding `prob_badKeyIndFgDh4At_le_gapDh`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Opk

open Proofs.SignalPqxdh.Security.FgGapDh

/-! ## Simple queries -/

theorem fgStepCoupling_dh4_unchanged (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (r : KeyIndResponse)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[k1 (r, hst)] {true} ≤ 𝒟[k2 (r, st)] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact hCont r hst st hDead ⟨h1, h2, h3, by omega, by omega, h6, h7, h8, h9, h10, h11⟩

theorem fgStepCoupling_dh4_initPrin (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.initPrin u)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := by
    rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, hPrinEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKA0 hSec0 => ?_)
    have hLen0 : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
    let entry : PrincipalEntry := {
      secIKA0 := secIKA0, ikAPk := P.x25519Base secIKA0,
      secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
    apply hCont (.initPrinResp entry.ikAPk entry.ikSignPk)
    · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]
      exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hOpkV,
        ?_, hSpks, hOpks, hSess⟩
      · exact ⟨(validPrincipals_cons S u entry hst.base.principals hValidEc.1 hAny).1,
          hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen0, rfl⟩
        · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh4_corruptIK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.corruptIK u)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinEq, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    simp only [StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont
  | some p =>
    rcases p with ⟨_, entry⟩
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    apply hCont (.corrResp entry.secIKA0 entry.secIKAsign)
    · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]
      exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hOpkV,
        ?_, hSpks, hOpks, hSess⟩
      · exact ⟨(validPrincipals_map_corrupted S P u.val hst.base.principals hValidEc.1).1,
          hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
      · intro kv hkv
        rw [List.mem_map] at hkv
        rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
        have hPr := hPrins (idx, e) heMem
        by_cases hIdx : idx == u.val <;> simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq <;>
          (subst hEq; exact hPr)

theorem fgStepCoupling_dh4_genOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImplOpk sIdx oIdx (some uSk) (some vSk) S P (.genOPK u j o)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPureOpk P P.isValidDhTriple sIdx oIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genOPK u j o) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hOpkAnyEq : st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) =
      hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) := by
    rw [hBaseEq]; exact any_idx_eraseOpkEntriesFg S oIdx (u.val, j.val, o.val) hst.base.opkEntries
  unfold pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase fgKeyIndStepPureOpk fgGenOPKPureOpk
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpkAnyEq, bind_assoc, pure_bind]
  cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hSlotEq : opkFlatIdx S u j o = opkSlotFlatIdx S (u.val, j.val, o.val) := rfl
    by_cases hTgt : (opkFlatIdx S u j o == oIdx) = true
    · have hTgtV : (opkSlotFlatIdx S (u.val, j.val, o.val) == oIdx) = true := hTgt
      simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, evalDist_sampleScalar32_const]
      let oEntry : OpkEntry := { opkSk := vSk, opkPk := P.x25519Base vSk, consumed := false }
      have hOpkV' : opkTargetIsV oIdx (P.x25519Base vSk)
          { hst with base := { hst.base with opkEntries :=
            ((u.val, j.val, o.val), oEntry) :: hst.base.opkEntries } } = true := by
        unfold opkTargetIsV at hOpkV ⊢
        simp [List.all_cons, oEntry, hOpkV]
      apply hCont (.pkResp (P.x25519Base vSk))
      · unfold deadDh4 at hDead ⊢
        rw [hOpkV']
        rw [hOpkV] at hDead
        exact hDead
      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hOpkV', hPrins, hSpks,
          ?_, hSess⟩
        · rw [hBaseEq]
          simp [eraseStateFgOpk, eraseOpkEntriesFg, eraseOpkEntryFg, beq_iff_eq.mp hTgtV]
        · exact ⟨hValidEc.1, hValidEc.2.1,
            (validOpkEntries_cons S u j o oEntry hst.base.opkEntries hValidEc.2.2.1 hAny).1,
            hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hvSk, rfl, fun _ => rfl⟩
          · exact hOpks kv hMem
    · have hTgtF : (opkFlatIdx S u j o == oIdx) = false := Bool.eq_false_iff.mpr hTgt
      have hTgtVF : (opkSlotFlatIdx S (u.val, j.val, o.val) == oIdx) = false := hTgtF
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun opkSk hOpk => ?_)
      have hLen : opkSk.length = 32 := length_of_mem_support_sampleScalar32 hOpk
      let oEntry : OpkEntry := { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false }
      have hOpkV' : opkTargetIsV oIdx (P.x25519Base vSk)
          { hst with base := { hst.base with opkEntries :=
            ((u.val, j.val, o.val), oEntry) :: hst.base.opkEntries } } = true := by
        unfold opkTargetIsV at hOpkV ⊢
        simp [List.all_cons, hTgtVF, hOpkV]
      apply hCont (.pkResp (P.x25519Base opkSk))
      · unfold deadDh4 at hDead ⊢
        rw [hOpkV']
        rw [hOpkV] at hDead
        exact hDead
      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hOpkV', hPrins, hSpks,
          ?_, hSess⟩
        · rw [hBaseEq]
          simp [eraseStateFgOpk, eraseOpkEntriesFg, eraseOpkEntryFg, beq_eq_false_iff_ne.mp hTgtVF]
        · exact ⟨hValidEc.1, hValidEc.2.1,
            (validOpkEntries_cons S u j o oEntry hst.base.opkEntries hValidEc.2.2.1 hAny).1,
            hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hLen, rfl, fun h => by rw [hTgtVF] at h; cases h⟩
          · exact hOpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh4_genSPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.genSPK u j)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
  have hTgtF : (spkBundleFlatIdx S u j == noSpkIdx S) = false :=
    spkBundleFlatIdx_ne_noSpkIdx S u j
  unfold pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkEq, hPrinEq, bind_assoc, pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, sampleKemKeyGen, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun spkSk hSpkSk => ?_)
      have hSpkLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpkSk
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
      refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
      let spkPk := P.x25519Base spkSk
      let pqspkPk := (P.kemKeyGen seedKem).1
      let pqspkSk := (P.kemKeyGen seedKem).2
      let bEntry1 : SpkBundleEntry := {
        spkSk := spkSk, spkPk := spkPk,
        spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk,
        pqspkSk := pqspkSk, pqspkPk := pqspkPk,
        pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
      let bundleOut : PreKeyBundleInput := {
        ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
        spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
        pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
      apply hCont (.bundleResp bundleOut)
      · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]
        exact hDead
      · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hOpkV,
          hPrins, ?_, hOpks, hSess⟩
        · exact ⟨hValidEc.1,
            (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
            hValidEc.2.2.1, hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hSpkLen, rfl⟩
          · exact hSpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh4_roQuery (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (secrets : Bytes) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.roQuery secrets)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roQuery secrets) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
  rcases fgRoQueryPure_eq_or_sample (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) hCache with
    ⟨dk, hEval, hFg⟩ | ⟨newRaw, newFgL, hEval, hFg, hStepCache⟩
  · rw [hEval, hFg]
    simp only [pure_bind]
    apply hCont (.drKeyResp dk)
    · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
    · refine ⟨hBaseEq, ⟨by rw [hAdvEq.1], hAdvEq.2⟩, hCache, by dsimp; omega,
        by dsimp [List.length_cons]; omega,
        hValidEc, hOpkV, hPrins, hSpks, hOpks, hSess⟩
  · rw [hEval, hFg]
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun dk _ => ?_)
    rcases hStepCache dk (by omega) with ⟨hLenNew, hCacheNew⟩
    apply hCont (.drKeyResp dk)
    · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
    · refine ⟨hBaseEq, ⟨by rw [hAdvEq.1], hAdvEq.2⟩, hCacheNew, by dsimp; omega,
        by dsimp [List.length_cons]; omega,
        hValidEc, hOpkV, hPrins, hSpks, hOpks, hSess⟩

theorem fgStepCoupling_dh4_revealDhSecrets (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P .revealDhSecrets).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) .revealDhSecrets st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, ↓reduceIte,
    StateT.run_pure, pure_bind]
  exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv
    .noneResp k1 k2 hCont

private theorem deadDh4_map_tested {S : Setup} (P : Primitives) (sIdx oIdx : ℕ) (V : Bytes)
    (sid : SessionId S) (hst : KeyIndFgCutoffState S) :
    deadDh4 P sIdx oIdx V
      { hst with base := { hst.base with sessions := hst.base.sessions.map (fun s =>
          if s.sid == sid then { s with tested := true } else s) } } =
      deadDh4 P sIdx oIdx V hst := by
  unfold deadDh4 opkTargetIsV
  have hF : (hst.base.sessions.map (fun s =>
      if s.sid == sid then { s with tested := true } else s)).find?
        (fun s => initSessionSlotIdx s.sid == sIdx) =
      (hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        (fun s => if s.sid == sid then { s with tested := true } else s) := by
    rw [List.find?_map]
    congr 1; congr 1; funext s; dsimp only [Function.comp_def]; cases s.sid == sid <;> rfl
  rw [hF]
  cases hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s => dsimp only [Option.map]; cases s.sid == sid <;> rfl

private theorem deadDh4_map_revealed {S : Setup} (P : Primitives) (sIdx oIdx : ℕ) (V : Bytes)
    (sid : SessionId S) (hst : KeyIndFgCutoffState S) :
    deadDh4 P sIdx oIdx V
      { hst with base := { hst.base with sessions := hst.base.sessions.map (fun s =>
          if s.sid == sid then { s with revealed := true } else s) } } =
      deadDh4 P sIdx oIdx V hst := by
  unfold deadDh4 opkTargetIsV
  have hF : (hst.base.sessions.map (fun s =>
      if s.sid == sid then { s with revealed := true } else s)).find?
        (fun s => initSessionSlotIdx s.sid == sIdx) =
      (hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        (fun s => if s.sid == sid then { s with revealed := true } else s) := by
    rw [List.find?_map]
    congr 1; congr 1; funext s; dsimp only [Function.comp_def]; cases s.sid == sid <;> rfl
  rw [hF]
  cases hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s => dsimp only [Option.map]; cases s.sid == sid <;> rfl

theorem fgStepCoupling_dh4_testSession (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.testSession sid)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.testSession sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hFreshEq : isKeyIndSessionTestable st.base sid = isKeyIndSessionTestable hst.base sid := by
    rw [hBaseEq]; exact isFreshKeyIndSession_eraseStateFgOpk sIdx oIdx hst.base sid
  have hSecbEq : st.base.secb = hst.base.secb := by rw [hBaseEq]; rfl
  have hRespEq : st.base.respSessions = hst.base.respSessions := by rw [hBaseEq]; rfl
  have hSessFind : st.base.sessions.find? (fun e => e.sid == sid) =
      (hst.base.sessions.find? (fun e => e.sid == sid)).map (eraseSessionEntryFg sIdx) := by
    rw [hBaseEq]; exact find?_sid_eraseSessionsFg sIdx sid hst.base.sessions
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hFreshEq, hSessFind, hRespEq, hSecbEq,
    bind_assoc, pure_bind]
  cases hFr : isKeyIndSessionTestable hst.base sid
  · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hFS : hst.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only [Option.map]
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        eraseSessionEntryFg_drKeyReal, eraseSessionEntryFg_drKeyRand]
      apply hCont (.drKeyResp (if hst.base.secb then e.drKeyReal else e.drKeyRand))
      · rw [deadDh4_map_tested]; exact hDead
      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
          validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl ?_, hOpkV, hPrins, hSpks, hOpks, ?_⟩
        · rw [hBaseEq]; dsimp [eraseStateFgOpk]; rw [test_map_eraseSessionsFg]
        · rw [List.map_map]; refine List.map_congr_left (fun s _ => ?_)
          dsimp; cases s.sid == sid <;> rfl
        · intro s hs
          rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
          cases s0.sid == sid <;> exact hSess s0 hs0
    | none =>
      dsimp only [Option.map]
      cases hFR : hst.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      | some r =>
        dsimp only
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        apply hCont (.drKeyResp (if hst.base.secb then r.drKeyReal else r.drKeyRand))
        · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
        · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
            validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hOpkV, hPrins, hSpks, hOpks, hSess⟩

theorem fgStepCoupling_dh4_revealSessionKey (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.revealSessionKey
      sid)).run hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.revealSessionKey sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hRespEq : st.base.respSessions = hst.base.respSessions := by rw [hBaseEq]; rfl
  have hSessFind : st.base.sessions.find? (fun e => e.sid == sid) =
      (hst.base.sessions.find? (fun e => e.sid == sid)).map (eraseSessionEntryFg sIdx) := by
    rw [hBaseEq]; exact find?_sid_eraseSessionsFg sIdx sid hst.base.sessions
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSessFind, hRespEq, bind_assoc,
    pure_bind]
  cases hFS : hst.base.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    dsimp only [Option.map]
    simp only [eraseSessionEntryFg_tested, eraseSessionEntryFg_drKeyReal]
    cases hT : e.tested
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind]
      apply hCont (.drKeyResp e.drKeyReal)
      · rw [deadDh4_map_revealed]; exact hDead
      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
          validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl ?_, hOpkV, hPrins, hSpks, hOpks, ?_⟩
        · rw [hBaseEq]; dsimp [eraseStateFgOpk]; rw [reveal_map_eraseSessionsFg]
        · rw [List.map_map]; refine List.map_congr_left (fun s _ => ?_)
          dsimp; cases s.sid == sid <;> rfl
        · intro s hs
          rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
          cases s0.sid == sid <;> exact hSess s0 hs0
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
  | none =>
    dsimp only [Option.map]
    cases hFR : hst.base.respSessions.find? (fun r => r.sid == sid) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some r =>
      dsimp only
      cases hT : r.tested
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind]
        apply hCont (.drKeyResp r.drKeyReal)
        · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
        · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
            validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hOpkV, hPrins, hSpks, hOpks, hSess⟩
      · simp only [↓reduceIte, StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont

theorem fgStepCoupling_dh4_registerKey (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sk : Bytes) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.registerKey sk)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.registerKey sk) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl registerAdvKey liftFgBase
    fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
  by_cases hLen : (sk.length != 32) = true
  · simp only [hLen, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont
  · have hSkLen32 : sk.length = 32 := by
      cases hEq : (sk.length == 32)
      · simp [bne, hEq] at hLen
      · exact beq_iff_eq.mp hEq
    simp only [hLen, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind]
    apply hCont (.pkResp (P.x25519Base sk))
    · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, ⟨hAdvEq.1, by rw [hAdvEq.2.1]; rfl, ?_⟩,
        hCache, by dsimp; omega, by dsimp; omega,
        validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hOpkV, hPrins, hSpks, hOpks, hSess⟩
      intro kv hkv
      rcases List.mem_cons.mp hkv with rfl | hMem
      · exact ⟨hSkLen32, rfl⟩
      · exact hAdvEq.2.2 kv hMem


/-! ## Accept and initiate queries -/

private theorem not_beq_true_eq_false' {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

private theorem of_not_not_eq_true' {b : Bool} (h : ¬((!b) = true)) : b = true := by
  cases b <;> simp_all

private theorem hdr_noOpk_extract' {S : Setup} {j : Fin S.N_recv} {hdr : HandshakeHdr}
    (h : ¬(!(hdr.spkId == UInt32.ofNat j.val &&
             hdr.pqspkId == UInt32.ofNat j.val &&
             hdr.opkId? == none &&
             hdr.ikAPk.length == 32 &&
             hdr.ekAPk.length == 32)) = true) :
    hdr.opkId? = none ∧ hdr.ikAPk.length = 32 ∧ hdr.ekAPk.length = 32 := by
  have h1 := of_not_not_eq_true' h
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1.1.2, h1.1.2, h1.2⟩

private theorem hdr_opk_extract' {S : Setup} {j : Fin S.N_recv} {o : Fin S.N_opk} {hdr :
    HandshakeHdr}
    (h : ¬(!(hdr.spkId == UInt32.ofNat j.val &&
             hdr.pqspkId == UInt32.ofNat j.val &&
             hdr.opkId? == some (UInt32.ofNat o.val) &&
             hdr.ikAPk.length == 32 &&
             hdr.ekAPk.length == 32)) = true) :
    hdr.opkId? = some (UInt32.ofNat o.val) ∧ hdr.ikAPk.length = 32 ∧ hdr.ekAPk.length = 32 := by
  have h1 := of_not_not_eq_true' h
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1.1.2, h1.1.2, h1.2⟩

private theorem and_dup_last (a b c d : Bool) : (a && b && c && d && d) = (a && b && c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The DH4 check in `acceptKeys` is redundant with the `dh2Zero` check: both are equivalent to
    `ekAPk` not being a small-order point (`WellFormedPrimitives.x25519_zero_iff`). -/
theorem acceptKeys_opk_eq_none_or_some_dh4 (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (ikBSk ikBPk spkBSk spkBPk opkSk pqspkBSk pqspkBPk : Bytes)
    (replayOk : Bool) (hdr : HandshakeHdr) (opkId : UInt32)
    (hOpk : hdr.opkId? = some opkId)
    (hIkLen : hdr.ikAPk.length = 32) (hEkLen : hdr.ekAPk.length = 32) :
    (Model.acceptKeys P {
      ikBSk := ikBSk, ikBPk := ikBPk, spkBSk := spkBSk, spkBPk := spkBPk,
      opkBSk? := some opkSk, pqspkBSk := pqspkBSk, pqspkBPk := pqspkBPk,
      trustedPeer := true, replayOk := replayOk, hdr := hdr }).isSome =
    ((replayOk && P.isCanonical hdr.ekAPk &&
      P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
      P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0) &&
     (P.kemDecaps pqspkBSk hdr.kemCt).isSome) := by
  rw [acceptKeys_opk_eq_none_or_some P hP ikBSk ikBPk spkBSk spkBPk opkSk pqspkBSk pqspkBPk
    replayOk hdr opkId hOpk hIkLen hEkLen,
    bne_x25519_zero_eq P hP.toWellFormedPrimitivesδ opkSk hdr.ekAPk hEkLen,
    and_dup_last]

theorem koskBundleOkTake_eq_of_le (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) :
    koskBundleOkTake S P principals spkBundles opkEntries advKeyPows bundle =
    koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  unfold koskBundleOkTake koskBundleOk isGameIdKey
  rw [List.take_of_length_le hP, List.take_of_length_le hS, List.take_of_length_le hO, hAdvPows]
  simp only [isAdvRegisteredPows_map_eq]
  cases bundle.opkB? with
  | none => rfl
  | some p =>
    rcases p with ⟨_, opkPk⟩
    rfl

theorem onCurveKeyLocal_spk_of_koskBundleOk (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput)
    (hSpks : ∀ kv ∈ spkBundles, kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk)
    (hAdv : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hNotKosk : (!koskBundleOk P principals spkBundles opkEntries advKeys bundle) = true → False) :
    onCurveKeyLocal P bundle.spkB := by
  have hKosk : koskBundleOk P principals spkBundles opkEntries advKeys bundle = true := by
    cases h : koskBundleOk P principals spkBundles opkEntries advKeys bundle
    · exfalso; exact hNotKosk (by simp [h])
    · rfl
  unfold koskBundleOk at hKosk
  rcases (Bool.and_eq_true _ _).mp hKosk with ⟨h12, _⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨_, h2⟩
  rcases (Bool.or_eq_true _ _).mp h2 with hGame | hReg
  · unfold isGameSpk at hGame
    rcases List.any_eq_true.mp hGame with ⟨⟨idx0, b⟩, hMem, hBeq⟩
    rcases hSpks (idx0, b) hMem with ⟨hLen, hPk0⟩
    have hPow : P.pow8 bundle.spkB = P.pow8 (P.x25519Base b.spkSk) := by
      rw [← hPk0, (beq_iff_eq.mp hBeq).symm]
    exact Or.inr ⟨b.spkSk, hLen, hPow⟩
  · exact onCurveKeyLocal_of_isAdvRegistered P advKeys bundle.spkB hAdv hReg

theorem computeTwoSideOrPairPosPure_eraseOpk_fgPosRightRep
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (S : Setup) (oIdx : ℕ)
    (vSk : Bytes) (k : ℕ × ℕ × ℕ) (oEntry : OpkEntry) (pk : Bytes)
    (ho : oEntry.opkSk.length = 32 ∧ oEntry.opkPk = P.x25519Base oEntry.opkSk ∧
      ((opkSlotFlatIdx S k == oIdx) = true → oEntry.opkSk = vSk))
    (hpk : onCurveKeyLocal P pk) :
    FgPosRightRep P vSk
      (computeTwoSideOrPairPosPure P [] (eraseOpkEntryFg S oIdx k oEntry).opkSk pk oEntry.opkPk)
      (P.x25519 oEntry.opkSk pk) := by
  dsimp only [eraseOpkEntryFg]
  by_cases hIdx : (opkSlotFlatIdx S k == oIdx) = true
  · have hSk : oEntry.opkSk = vSk := ho.2.2 hIdx
    have hPk : oEntry.opkPk = P.x25519Base vSk := by rw [ho.2.1, hSk]
    simp only [hIdx, ↓reduceIte, computeTwoSideOrPairPosPure_nil_nil, hPk, hSk]
    exact fgPosRightRep_mkPair_right P hP.toWellFormedPrimitivesδ vSk pk hpk
  · have hIdxF : (opkSlotFlatIdx S k == oIdx) = false := Bool.eq_false_iff.mpr hIdx
    simp only [hIdxF, Bool.false_eq_true, ↓reduceIte,
      computeTwoSideOrPairPosPure_nil_right_len32 P oEntry.opkSk pk oEntry.opkPk ho.1]
    exact fgPosRightRep_mkSecret P vSk _ (hP.x25519_len _ _)

theorem deadDh4_consume {S : Setup} (P : Primitives) (sIdx oIdx : ℕ) (V : Bytes)
    (key : ℕ × ℕ × ℕ) (hst hst' : KeyIndFgCutoffState S)
    (hOpk : hst'.base.opkEntries = hst.base.opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e)))
    (hSess : hst'.base.sessions = hst.base.sessions) :
    deadDh4 P sIdx oIdx V hst' = deadDh4 P sIdx oIdx V hst := by
  unfold deadDh4 opkTargetIsV
  rw [hOpk, hSess, opkTargetIsV_consume]

theorem fgStepCoupling_dh4_acceptNoOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.acceptNoOPK k j l
      hdr)).run hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.acceptNoOPK k j l hdr) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hUsedEq : st.base.usedRecvNoOPK = hst.base.usedRecvNoOPK := by rw [hBaseEq]; rfl
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  have hKyberEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := by rw [hBaseEq]; rfl
  have hSessEq : st.base.sessions = eraseSessionsFg sIdx hst.base.sessions := by rw [hBaseEq]; rfl
  have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
  have hKoskEq : koskSenderOkTake S P hst.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk :=
    koskSenderOkTake_eq_koskSenderOk S P hst.base.principals st.advKeyPows hst.base.advKeys
      hdr.ikAPk
      hLengths.1 hAdvEq.2.1
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
    fgRunAcceptNoOPKPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hUsedEq, hPrinEq, hKyberEq, hKoskEq,
    hSpkEq,
    bind_assoc, pure_bind]
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    rcases hdr_noOpk_extract' hHdr with ⟨hOpkNone, hIkLen, hEkLen⟩
    by_cases hUsed : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      | some pk =>
        rcases pk with ⟨k0, kEntry⟩
        dsimp only
        have hkMem := List.mem_of_find?_eq_some hFK
        rcases hPrins (k0, kEntry) hkMem with ⟨hkSkLen, hkPk⟩
        cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
            hInv0 .noneResp k1 k2 hCont
        | some pb =>
          rcases pb with ⟨kb0, bEntry⟩
          dsimp only
          have hbMem := List.mem_of_find?_eq_some hFB
          rcases hSpks (kb0, bEntry) hbMem with ⟨hbSkLen, hbPk⟩
          have hAccSome := acceptKeys_noOpk_eq_none_or_some P hP
            kEntry.secIKA0 kEntry.ikAPk bEntry.spkSk bEntry.spkPk bEntry.pqspkSk bEntry.pqspkPk
            (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
              hdr.ekAPk).1
            hdr hOpkNone hIkLen hEkLen
          by_cases hChk : (!((checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId
               hdr.spkId hdr.ekAPk).1 &&
               P.isCanonical hdr.ekAPk &&
               P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
               P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0)) = true
          · have hChkF := not_beq_true_eq_false' hChk
            have hAccNone : Model.acceptKeys P {
                ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk, spkBPk :=
                  bEntry.spkPk,
                opkBSk? := none, pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                trustedPeer := true,
                replayOk := (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId
                  hdr.spkId hdr.ekAPk).1,
                hdr := hdr } = none := by
              rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkF,
                Bool.false_and]
            simp only [hAccNone, hChk, ↓reduceIte, StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
          · have hChkT := of_not_not_eq_true' hChk
            simp only [hChk, Bool.false_eq_true, ↓reduceIte]
            cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
            | none =>
              have hAccNone : Model.acceptKeys P {
                  ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk :=
                    bEntry.spkSk, spkBPk := bEntry.spkPk,
                  opkBSk? := none, pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                  trustedPeer := true,
                  replayOk := (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId
                    hdr.spkId hdr.ekAPk).1,
                  hdr := hdr } = none := by
                rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkT, hDec]; rfl
              simp only [hAccNone, StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some ss =>
              have hAccIsSome : (Model.acceptKeys P {
                  ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk :=
                    bEntry.spkSk, spkBPk := bEntry.spkPk,
                  opkBSk? := none, pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                  trustedPeer := true,
                  replayOk := (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId
                    hdr.spkId hdr.ekAPk).1,
                  hdr := hdr }).isSome = true := by
                rw [hAccSome, hChkT, hDec]; rfl
              obtain ⟨accOut, hAccOut⟩ := Option.isSome_iff_exists.mp hAccIsSome
              simp only [hAccOut]
              let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
              let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
              let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
              let pos1 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
              let pos2 := computeTwoSideOrPairPosPure P [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
              let pos3 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
              have hPos1 : FgPosRightRep P vSk pos1 dh1 := by
                dsimp only [pos1, dh1]
                rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ikAPk
                  bEntry.spkPk hbSkLen]
                exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec1 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos2 : FgPosLeftRep P uSk pos2 dh2 := by
                dsimp only [pos2, dh2]
                rw [computeTwoSideOrPairPosPure_nil_right_len32 P kEntry.secIKA0 hdr.ekAPk
                  kEntry.ikAPk hkSkLen]
                exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec2 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos3 : FgPosLeftRep P uSk pos3 dh3 := by
                dsimp only [pos3, dh3]
                rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ekAPk
                  bEntry.spkPk hbSkLen]
                exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec3 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hTup : FgTupleRel (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) pos1 pos2 pos3 none
                dh1 dh2 dh3 none ss :=
                ⟨hPos1, hPos2, hPos3, trivial, hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _ hDec⟩
              have hTakePrin : hst.base.principals.take S.N_dh = hst.base.principals :=
                List.take_of_length_le hLengths.1
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind, hTakePrin]
              rcases fgPatchPure_eq_or_sample (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) hCache
                hTup with
                ⟨drKey, hEval, hFg⟩ | ⟨hEval, hFg, hStepCache⟩
              · rw [hEval, hFg]
                simp only [pure_bind, hSessEq, choosePartnerDrKeyRandPure_eraseSessionsFg]
                rw [recordKeyIndResp_run_eq_choosePartnerDrKeyRandPure P _ _ (by dsimp; exact
                  hLengths.2.2.2)]
                simp only [bind_assoc, pure_bind]
                refine evalDist_bind_true_mono_of_support
                  (choosePartnerDrKeyRandPure P hst.base.sessions _) _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals hdr.ikAPk with
                | some _ =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont .acceptFreshResp
                  · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
                  · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                      validKeyIndEcFg_acceptNoOPK k j l hValidEc hUsed, hOpkV, hPrins, hSpks,
                        hOpks, hSess⟩
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont (.drKeyResp drKey)
                  · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
                  · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                      validKeyIndEcFg_acceptNoOPK k j l hValidEc hUsed, hOpkV, hPrins, hSpks,
                        hOpks, hSess⟩
              · rw [hEval, hFg]
                simp only [bind_assoc, pure_bind]
                refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun drKey _ => ?_)
                have hCacheNew := hStepCache drKey (by omega)
                simp only [hSessEq, choosePartnerDrKeyRandPure_eraseSessionsFg]
                rw [recordKeyIndResp_run_eq_choosePartnerDrKeyRandPure P _ _ (by dsimp; exact
                  hLengths.2.2.2)]
                simp only [bind_assoc, pure_bind]
                refine evalDist_bind_true_mono_of_support
                  (choosePartnerDrKeyRandPure P hst.base.sessions _) _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals hdr.ikAPk with
                | some _ =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont .acceptFreshResp
                  · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
                  · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCacheNew,
                      by dsimp [List.length_cons]; omega, by dsimp; omega,
                      validKeyIndEcFg_acceptNoOPK k j l hValidEc hUsed, hOpkV, hPrins, hSpks,
                        hOpks, hSess⟩
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont (.drKeyResp drKey)
                  · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
                  · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCacheNew,
                      by dsimp [List.length_cons]; omega, by dsimp; omega,
                      validKeyIndEcFg_acceptNoOPK k j l hValidEc hUsed, hOpkV, hPrins, hSpks,
                        hOpks, hSess⟩

theorem fgStepCoupling_dh4_acceptOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.acceptOPK k j o
      hdr)).run hst >>= k1] {true} ≤
      𝒟[fgRunAcceptOPKPureOpk P P.isValidDhTriple S b.q_total k j o hdr st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hUsedEq : st.base.usedRecvOPK = hst.base.usedRecvOPK := by rw [hBaseEq]; rfl
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
  have hKyberEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := by rw [hBaseEq]; rfl
  have hSessEq : st.base.sessions = eraseSessionsFg sIdx hst.base.sessions := by rw [hBaseEq]; rfl
  have hKoskEq : koskSenderOkTake S P hst.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk :=
    koskSenderOkTake_eq_koskSenderOk S P hst.base.principals st.advKeyPows hst.base.advKeys
      hdr.ikAPk
      hLengths.1 hAdvEq.2.1
  have hOpkFind : st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) =
      (hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))).map
        (fun (idx, e) => (idx, eraseOpkEntryFg S oIdx idx e)) := by
    rw [hBaseEq]; exact find?_idx_eraseOpkEntriesFg S oIdx (k.val, j.val, o.val) hst.base.opkEntries
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgRunAcceptOPKPureOpk
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hUsedEq, hPrinEq, hSpkEq, hKyberEq,
    hKoskEq,
    hOpkFind, bind_assoc, pure_bind]
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    rcases hdr_opk_extract' hHdr with ⟨hOpkSome, hIkLen, hEkLen⟩
    by_cases hUsed : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      | some pk =>
        rcases pk with ⟨k0, kEntry⟩
        dsimp only
        have hkMem := List.mem_of_find?_eq_some hFK
        rcases hPrins (k0, kEntry) hkMem with ⟨hkSkLen, hkPk⟩
        cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
            hInv0 .noneResp k1 k2 hCont
        | some pb =>
          rcases pb with ⟨kb0, bEntry⟩
          dsimp only
          have hbMem := List.mem_of_find?_eq_some hFB
          rcases hSpks (kb0, bEntry) hbMem with ⟨hbSkLen, hbPk⟩
          cases hFO : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none =>
            dsimp only [Option.map]
            simp only [StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
          | some po =>
            rcases po with ⟨ko0, oEntry⟩
            dsimp only [Option.map]
            have hoMem := List.mem_of_find?_eq_some hFO
            have hoInv := hOpks (ko0, oEntry) hoMem
            simp only [eraseOpkEntryFg_consumed, eraseOpkEntryFg_opkPk]
            by_cases hCons : oEntry.consumed = true
            · simp only [hCons, ↓reduceIte, StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            · simp only [hCons, Bool.false_eq_true, ↓reduceIte]
              have hAccSome := acceptKeys_opk_eq_none_or_some_dh4 P hP
                kEntry.secIKA0 kEntry.ikAPk bEntry.spkSk bEntry.spkPk oEntry.opkSk bEntry.pqspkSk
                  bEntry.pqspkPk
                (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                  hdr.ekAPk).1
                hdr (UInt32.ofNat o.val) hOpkSome hIkLen hEkLen
              by_cases hChk : (!((checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                   hdr.pqspkId hdr.spkId hdr.ekAPk).1 &&
                   P.isCanonical hdr.ekAPk &&
                   P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                   P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0)) = true
              · have hChkF := not_beq_true_eq_false' hChk
                have hAccNone : Model.acceptKeys P {
                    ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk :=
                      bEntry.spkSk, spkBPk := bEntry.spkPk,
                    opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk, pqspkBPk :=
                      bEntry.pqspkPk,
                    trustedPeer := true,
                    replayOk := (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId
                      hdr.spkId hdr.ekAPk).1,
                    hdr := hdr } = none := by
                  rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkF,
                    Bool.false_and]
                simp only [hAccNone, hChk, ↓reduceIte, StateT.run_pure, pure_bind]
                exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
                  hDead hInv0 .noneResp k1 k2 hCont
              · have hChkT := of_not_not_eq_true' hChk
                simp only [hChk, Bool.false_eq_true, ↓reduceIte]
                cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                | none =>
                  have hAccNone : Model.acceptKeys P {
                      ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk :=
                        bEntry.spkSk, spkBPk := bEntry.spkPk,
                      opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk, pqspkBPk :=
                        bEntry.pqspkPk,
                      trustedPeer := true,
                      replayOk := (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                        hdr.pqspkId hdr.spkId hdr.ekAPk).1,
                      hdr := hdr } = none := by
                    rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkT,
                      hDec]; rfl
                  simp only [hAccNone, StateT.run_pure, pure_bind]
                  exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst
                    st hDead hInv0 .noneResp k1 k2 hCont
                | some ss =>
                  have hAccIsSome : (Model.acceptKeys P {
                      ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk :=
                        bEntry.spkSk, spkBPk := bEntry.spkPk,
                      opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk, pqspkBPk :=
                        bEntry.pqspkPk,
                      trustedPeer := true,
                      replayOk := (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                        hdr.pqspkId hdr.spkId hdr.ekAPk).1,
                      hdr := hdr }).isSome = true := by
                    rw [hAccSome, hChkT, hDec]; rfl
                  obtain ⟨accOut, hAccOut⟩ := Option.isSome_iff_exists.mp hAccIsSome
                  simp only [hAccOut]
                  let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
                  let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
                  let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
                  let dh4 := P.x25519 oEntry.opkSk hdr.ekAPk
                  let pos1 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
                  let pos2 := computeTwoSideOrPairPosPure P [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
                  let pos3 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
                  let pos4 := computeTwoSideOrPairPosPure P [] (eraseOpkEntryFg S oIdx ko0
                    oEntry).opkSk hdr.ekAPk oEntry.opkPk
                  have hPos1 : FgPosRightRep P vSk pos1 dh1 := by
                    dsimp only [pos1, dh1]
                    rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ikAPk
                      bEntry.spkPk hbSkLen]
                    exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec1 _
                      (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                  have hPos2 : FgPosLeftRep P uSk pos2 dh2 := by
                    dsimp only [pos2, dh2]
                    rw [computeTwoSideOrPairPosPure_nil_right_len32 P kEntry.secIKA0 hdr.ekAPk
                      kEntry.ikAPk hkSkLen]
                    exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec2 _
                      (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                  have hPos3 : FgPosLeftRep P uSk pos3 dh3 := by
                    dsimp only [pos3, dh3]
                    rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ekAPk
                      bEntry.spkPk hbSkLen]
                    exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec3 _
                      (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                  have hEkOnCurve : onCurveKeyLocal P hdr.ekAPk :=
                    Or.inl (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp
                      (Bool.and_eq_true _ _ |>.mp hChkT).1).1).2
                  have hPos4 : FgOptRightRep P vSk (some pos4) (some dh4) :=
                    computeTwoSideOrPairPosPure_eraseOpk_fgPosRightRep P hP S oIdx vSk ko0 oEntry
                      hdr.ekAPk hoInv hEkOnCurve
                  have hTup : FgTupleRel (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) pos1 pos2 pos3
                    (some pos4) dh1 dh2 dh3 (some dh4) ss :=
                    ⟨hPos1, hPos2, hPos3, hPos4, hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _ hDec⟩
                  have hTakePrin : hst.base.principals.take S.N_dh = hst.base.principals :=
                    List.take_of_length_le hLengths.1
                  have hValidOpk' : ValidOpkEntries S (hst.base.opkEntries.map (fun (idx, e) =>
                      if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                        true }) else (idx, e))) :=
                    (validOpkEntries_map_consumed S P (k.val, j.val,
                      o.val) hst.base.opkEntries hValidEc.2.2.1).1
                  have hOpks' : ∀ kv ∈ hst.base.opkEntries.map (fun (idx, e) =>
                      if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                        true }) else (idx, e)),
                      kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk ∧
                      ((opkSlotFlatIdx S kv.1 == oIdx) = true → kv.2.opkSk = vSk) := by
                    intro kv hkv
                    rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
                    have hO := hOpks (idx, e) heMem
                    by_cases hIdx : idx == (k.val, j.val, o.val) <;>
                      simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq <;>
                      (subst hEq; exact hO)
                  have hBase' : ∀ (respSessions' : List (KeyIndRespEntry S)) (usedTriples' : List
                      (ℕ × UInt32 × UInt32 × Bytes)),
                      { st.base with
                        opkEntries :=
                          (eraseOpkEntriesFg S oIdx hst.base.opkEntries).map (fun (idx, e) =>
                          if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                            true }) else (idx, e))
                        usedRecvOPK := (k.val, j.val, o.val) :: hst.base.usedRecvOPK
                        seenKyberBaseKeys := usedTriples'
                        respSessions := respSessions' } =
                      eraseStateFgOpk sIdx oIdx { hst.base with
                        opkEntries := hst.base.opkEntries.map (fun (idx, e) =>
                          if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                            true }) else (idx, e))
                        usedRecvOPK := (k.val, j.val, o.val) :: hst.base.usedRecvOPK
                        seenKyberBaseKeys := usedTriples'
                        respSessions := respSessions' } := by
                    intro respSessions' usedTriples'
                    rw [consume_map_eraseOpkEntriesFg, hBaseEq]; rfl
                  have hOpkV' : ∀ hst' : KeyIndFgCutoffState S,
                      hst'.base.opkEntries = hst.base.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                          true }) else (idx, e)) →
                      opkTargetIsV oIdx (P.x25519Base vSk) hst' = true := by
                    intro hst' h
                    unfold opkTargetIsV at hOpkV ⊢
                    rw [h, opkTargetIsV_consume]; exact hOpkV
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind, hTakePrin]
                  rcases fgPatchPure_eq_or_sample (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) hCache
                    hTup with
                    ⟨drKey, hEval, hFg⟩ | ⟨hEval, hFg, hStepCache⟩
                  · rw [hEval, hFg]
                    simp only [pure_bind, hSessEq, choosePartnerDrKeyRandPure_eraseSessionsFg]
                    rw [recordKeyIndResp_run_eq_choosePartnerDrKeyRandPure P _ _ (by dsimp; exact
                      hLengths.2.2.2)]
                    simp only [bind_assoc, pure_bind]
                    refine evalDist_bind_true_mono_of_support
                      (choosePartnerDrKeyRandPure P hst.base.sessions _) _ _ (fun drKeyRand _ => ?_)
                    cases findHonestPrincipal P hst.base.principals hdr.ikAPk with
                    | some _ =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont .acceptFreshResp
                      · refine (deadDh4_consume P sIdx oIdx _ (k.val, j.val,
                          o.val) hst _ ?_ ?_).trans hDead <;> rfl
                      · refine ⟨by rw [hBaseEq]; simp only [eraseStateFgOpk, KeyIndState.mk.injEq,
                          and_true, true_and]; exact consume_map_eraseOpkEntriesFg S oIdx _ _,
                          hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                          validKeyIndEcFg_acceptOPK k j o hValidEc hValidOpk' hUsed, hOpkV' _ rfl,
                            hPrins, hSpks, hOpks', hSess⟩
                    | none =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont (.drKeyResp drKey)
                      · refine (deadDh4_consume P sIdx oIdx _ (k.val, j.val,
                          o.val) hst _ ?_ ?_).trans hDead <;> rfl
                      · refine ⟨by rw [hBaseEq]; simp only [eraseStateFgOpk, KeyIndState.mk.injEq,
                          and_true, true_and]; exact consume_map_eraseOpkEntriesFg S oIdx _ _,
                          hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                          validKeyIndEcFg_acceptOPK k j o hValidEc hValidOpk' hUsed, hOpkV' _ rfl,
                            hPrins, hSpks, hOpks', hSess⟩
                  · rw [hEval, hFg]
                    simp only [bind_assoc, pure_bind]
                    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun drKey _ => ?_)
                    have hCacheNew := hStepCache drKey (by omega)
                    simp only [hSessEq, choosePartnerDrKeyRandPure_eraseSessionsFg]
                    rw [recordKeyIndResp_run_eq_choosePartnerDrKeyRandPure P _ _ (by dsimp; exact
                      hLengths.2.2.2)]
                    simp only [bind_assoc, pure_bind]
                    refine evalDist_bind_true_mono_of_support
                      (choosePartnerDrKeyRandPure P hst.base.sessions _) _ _ (fun drKeyRand _ => ?_)
                    cases findHonestPrincipal P hst.base.principals hdr.ikAPk with
                    | some _ =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont .acceptFreshResp
                      · refine (deadDh4_consume P sIdx oIdx _ (k.val, j.val,
                          o.val) hst _ ?_ ?_).trans hDead <;> rfl
                      · refine ⟨by rw [hBaseEq]; simp only [eraseStateFgOpk, KeyIndState.mk.injEq,
                          and_true, true_and]; exact consume_map_eraseOpkEntriesFg S oIdx _ _,
                          hAdvEq, hCacheNew, by dsimp [List.length_cons]; omega, by dsimp; omega,
                          validKeyIndEcFg_acceptOPK k j o hValidEc hValidOpk' hUsed, hOpkV' _ rfl,
                            hPrins, hSpks, hOpks', hSess⟩
                    | none =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont (.drKeyResp drKey)
                      · refine (deadDh4_consume P sIdx oIdx _ (k.val, j.val,
                          o.val) hst _ ?_ ?_).trans hDead <;> rfl
                      · refine ⟨by rw [hBaseEq]; simp only [eraseStateFgOpk, KeyIndState.mk.injEq,
                          and_true, true_and]; exact consume_map_eraseOpkEntriesFg S oIdx _ _,
                          hAdvEq, hCacheNew, by dsimp [List.length_cons]; omega, by dsimp; omega,
                          validKeyIndEcFg_acceptOPK k j o hValidEc hValidOpk' hUsed, hOpkV' _ rfl,
                            hPrins, hSpks, hOpks', hSess⟩


theorem computeOptPosPure_left_len32_fgOptRightRep (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (vSk ekASk ekAPk : Bytes) (hLen : ekASk.length = 32)
    (opkB? : Option (UInt32 × Bytes)) :
    FgOptRightRep P vSk
      (computeOptPosPure P ekASk ekAPk (opkB?.map (fun (_, opkPk) => ([], opkPk))))
      (opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
  cases opkB? with
  | none => trivial
  | some p =>
    rcases p with ⟨opkId, opkPk⟩
    dsimp only [Option.map, computeOptPosPure]
    rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk opkPk hLen]
    exact fgPosRightRep_mkSecret P vSk _ (hWF.x25519_len ekASk opkPk)

theorem fgStepCoupling_dh4_initiate (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(do
        let x ← (fgPreInitiate false sIdx (some uSk) S P sid u bundle).run hst.base
        k1 (x.1, { base := x.2, advRoLog := hst.advRoLog }))] {true} ≤
      𝒟[fgRunInitiatePure P P.isValidDhTriple false sIdx S b.q_total
          (P.x25519Base uSk) sid u bundle st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hRespLen : hst.base.respSessions.length ≤ S.N_sess_tot :=
    validKeyIndEc_resp_length_le_fg S hst.base hValidEc
  have hRespEq : st.base.respSessions = hst.base.respSessions := by rw [hBaseEq]; rfl
  have hAnyEq : st.base.sessions.any (fun e => e.sid == sid) =
      hst.base.sessions.any (fun e => e.sid == sid) := by
    rw [hBaseEq]; exact any_sid_eraseSessionsFg sIdx sid hst.base.sessions
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
  have hOpkEq : st.base.opkEntries = eraseOpkEntriesFg S oIdx hst.base.opkEntries :=
    by rw [hBaseEq]; rfl
  have hTakePrin : hst.base.principals.take S.N_dh = hst.base.principals :=
    List.take_of_length_le hLengths.1
  have hKoskEq : koskBundleOkTake S P hst.base.principals hst.base.spkBundles
      (eraseOpkEntriesFg S oIdx hst.base.opkEntries) st.advKeyPows bundle =
      koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries hst.base.advKeys
        bundle := by
    rw [koskBundleOkTake_eraseOpk]
    exact koskBundleOkTake_eq_of_le S P hst.base.principals hst.base.spkBundles hst.base.opkEntries
      st.advKeyPows hst.base.advKeys bundle hLengths.1 hLengths.2.1 hLengths.2.2.1 hAdvEq.2.1
  have hProvEq : checkBundleProvenanceTake S P hst.base.principals hst.base.spkBundles
      (eraseOpkEntriesFg S oIdx hst.base.opkEntries) bundle =
      checkBundleProvenance P hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle
        := by
    rw [checkBundleProvenanceTake_eraseOpk]
    exact checkBundleProvenanceTake_eq_of_le S P hst.base.principals hst.base.spkBundles
      hst.base.opkEntries bundle hLengths.1 hLengths.2.1 hLengths.2.2.1
  unfold fgPreInitiate fgRunInitiatePure
  simp only [StateT.run_bind, StateT.run_get, hAnyEq, hPrinEq, hSpkEq, hOpkEq, hRespEq, hTakePrin,
    hKoskEq,
    Bool.not_false, Bool.true_and, pure_bind]
  cases hAny : hst.base.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hAnyMap : ((sessPksKeyInd S hst.base).map Prod.fst).any (fun s => s == sid) = false := by
      simp [sessPksKeyInd, List.any_map, Function.comp_def, hAny]
    have hValidSess' : ValidSessionIds S (sid :: (sessPksKeyInd S hst.base).map Prod.fst) :=
      (validSessionIds_cons S sid ((sessPksKeyInd S hst.base).map Prod.fst) hSend hValidEc.2.2.2.1
        hAnyMap).1
    cases hFU : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some pu =>
      rcases pu with ⟨u0, uEntry⟩
      dsimp only
      have huMem := List.mem_of_find?_eq_some hFU
      rcases hPrins (u0, uEntry) huMem with ⟨huSkLen, huPk⟩
      by_cases hKosk : (!koskBundleOk P hst.base.principals hst.base.spkBundles
        hst.base.opkEntries hst.base.advKeys bundle) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        by_cases hTgt : (initSessionSlotIdx sid == sIdx) = true
        · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind, evalDist_sampleScalar32_const]
          refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
          by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
               bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM
                 bundle.pqspkB) bundle.pqspkSig)) = true
          · simp only [hSig, ↓reduceIte, StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
          · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
            cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              dsimp only
              rcases Option.eq_none_or_eq_some bundle.opkB? with hOB | ⟨⟨opkId, opkPk⟩, hOB⟩
              ·
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind]
                refine le_trans (le_of_eq ?_) zero_le
                refine evalDist_bind_true_eq_zero_of_support _ _ (fun ⟨drKeyReal, roCache'⟩ _ => ?_)
                refine evalDist_bind_true_eq_zero_of_support _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals bundle.ikB with
                | some _ =>
                  simp only [StateT.run_pure, pure_bind]
                  exact hDeadCont _ _ (by unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp
                    [hOpkV, hTgt, hOB])
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  exact hDeadCont _ _ (by unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp
                    [hOpkV, hTgt, hOB])
              · by_cases hPowV : (P.pow8 opkPk == P.pow8 (P.x25519Base vSk)) = true
                · have hPowEq : P.pow8 opkPk = P.pow8 (P.x25519Base vSk) := beq_iff_eq.mp hPowV
                  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                  let dh2 := P.x25519 uSk bundle.ikB
                  let dh3 := P.x25519 uSk bundle.spkB
                  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 uSk opkPk)
                  let spkSk := lookupSpkSkTake S P hst.base.spkBundles st.advKeyPows bundle.spkB
                  let pos1 := computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk
                    bundle.spkB
                  let pos2 := computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.ikB
                  let pos3 := computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.spkB
                  let pos4? := computeOptPosPure P [] (P.x25519Base uSk) (bundle.opkB?.map (fun
                    (_, opkPk) => ([], opkPk)))
                  have hPos1 : FgPosRightRep P vSk pos1 dh1 := by
                    dsimp only [pos1, dh1]
                    rw [computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 spkSk uEntry.ikAPk
                      bundle.spkB huSkLen]
                    exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec1 _
                      (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                  have hIkOnCurve : onCurveKeyLocal P bundle.ikB :=
                    (onCurveKeyLocal_of_koskBundleOk P hst.base.principals hst.base.spkBundles
                      hst.base.opkEntries hst.base.advKeys bundle
                      hPrins (fun kv hkv => ⟨(hOpks kv hkv).1,
                        (hOpks kv hkv).2.1⟩) hAdvEq.2.2 hKosk).1
                  have hSpkOnCurve : onCurveKeyLocal P bundle.spkB :=
                    onCurveKeyLocal_spk_of_koskBundleOk P hst.base.principals hst.base.spkBundles
                      hst.base.opkEntries hst.base.advKeys bundle
                      hSpks hAdvEq.2.2 hKosk
                  have hPos2 : FgPosLeftRep P uSk pos2 dh2 := by
                    dsimp only [pos2, dh2, computeTwoSideOrPairPosPure_nil_nil]
                    exact fgPosLeftRep_mkPair_left P hP.toWellFormedPrimitivesδ uSk bundle.ikB
                      hIkOnCurve
                  have hPos3 : FgPosLeftRep P uSk pos3 dh3 := by
                    dsimp only [pos3, dh3, computeTwoSideOrPairPosPure_nil_nil]
                    exact fgPosLeftRep_mkPair_left P hP.toWellFormedPrimitivesδ uSk bundle.spkB
                      hSpkOnCurve
                  have hPos4 : FgOptRightRep P vSk pos4? dh4? := by
                    dsimp only [pos4?, dh4?]
                    rw [hOB]
                    dsimp only [Option.map, computeOptPosPure, computeTwoSideOrPairPosPure_nil_nil]
                    exact fgPosRightRep_mkPair_left_of_pow8 P hP.toWellFormedPrimitivesδ uSk vSk
                      opkPk huSk hvSk (hP.pow8_base_len opkPk vSk hPowEq) hPowEq
                  have hSsLen : ss.length = 32 :=
                    (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _ hEnc).1
                  have hTup : FgTupleRel (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) pos1 pos2 pos3
                    pos4? dh1 dh2 dh3 dh4? ss :=
                    ⟨hPos1, hPos2, hPos3, hPos4, hSsLen⟩
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind]
                  rcases fgPatchPure_eq_or_sample (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) hCache
                    hTup with
                    ⟨drKeyReal, hEval, hFg⟩ | ⟨hEval, hFg, hStepCache⟩
                  · rw [hEval, hFg]
                    simp only [pure_bind]
                    rw [chooseInitPartnerDrKeyRand_eq_pure P hst.base.respSessions _ _ hRespLen]
                    refine evalDist_bind_true_mono_of_support (chooseInitPartnerDrKeyRandPure P
                      hst.base.respSessions _) _ _ (fun drKeyRand _ => ?_)
                    cases findHonestPrincipal P hst.base.principals bundle.ikB with
                    | some _ =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont (.hdrResp _)
                      · unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp [hOpkV, hTgt, hOB,
                          hPowEq]
                      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                          ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess',
                            hValidEc.2.2.2.2⟩, hOpkV, hPrins, hSpks, hOpks, ?_⟩
                        · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg,
                            eraseSessionEntryFg, beq_iff_eq.mp hTgt, hProvEq]
                        · intro s hs
                          rcases List.mem_cons.mp hs with rfl | hMem
                          · exact ⟨huSk, rfl, fun _ => rfl⟩
                          · exact hSess s hMem
                    | none =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont (.initUnfreshResp drKeyReal _)
                      · unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp [hOpkV, hTgt, hOB,
                          hPowEq]
                      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                          ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess',
                            hValidEc.2.2.2.2⟩, hOpkV, hPrins, hSpks, hOpks, ?_⟩
                        · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg,
                            eraseSessionEntryFg, beq_iff_eq.mp hTgt, hProvEq]
                        · intro s hs
                          rcases List.mem_cons.mp hs with rfl | hMem
                          · exact ⟨huSk, rfl, fun _ => rfl⟩
                          · exact hSess s hMem
                  · rw [hEval, hFg]
                    simp only [bind_assoc, pure_bind]
                    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun drKeyReal _
                      => ?_)
                    have hCacheNew := hStepCache drKeyReal (by omega)
                    rw [chooseInitPartnerDrKeyRand_eq_pure P hst.base.respSessions _ _ hRespLen]
                    refine evalDist_bind_true_mono_of_support (chooseInitPartnerDrKeyRandPure P
                      hst.base.respSessions _) _ _ (fun drKeyRand _ => ?_)
                    cases findHonestPrincipal P hst.base.principals bundle.ikB with
                    | some _ =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont (.hdrResp _)
                      · unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp [hOpkV, hTgt, hOB,
                          hPowEq]
                      · refine ⟨?_, hAdvEq, hCacheNew, by dsimp [List.length_cons]; omega,
                          by dsimp; omega,
                          ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess',
                            hValidEc.2.2.2.2⟩, hOpkV, hPrins, hSpks, hOpks, ?_⟩
                        · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg,
                            eraseSessionEntryFg, beq_iff_eq.mp hTgt, hProvEq]
                        · intro s hs
                          rcases List.mem_cons.mp hs with rfl | hMem
                          · exact ⟨huSk, rfl, fun _ => rfl⟩
                          · exact hSess s hMem
                    | none =>
                      simp only [StateT.run_pure, pure_bind]
                      apply hCont (.initUnfreshResp drKeyReal _)
                      · unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp [hOpkV, hTgt, hOB,
                          hPowEq]
                      · refine ⟨?_, hAdvEq, hCacheNew, by dsimp [List.length_cons]; omega,
                          by dsimp; omega,
                          ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess',
                            hValidEc.2.2.2.2⟩, hOpkV, hPrins, hSpks, hOpks, ?_⟩
                        · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg,
                            eraseSessionEntryFg, beq_iff_eq.mp hTgt, hProvEq]
                        · intro s hs
                          rcases List.mem_cons.mp hs with rfl | hMem
                          · exact ⟨huSk, rfl, fun _ => rfl⟩
                          · exact hSess s hMem
                ·
                  have hPowNe : P.pow8 opkPk ≠ P.pow8 (P.x25519Base vSk) :=
                    fun h => hPowV (beq_iff_eq.mpr h)
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind]
                  refine le_trans (le_of_eq ?_) zero_le
                  refine evalDist_bind_true_eq_zero_of_support _ _ (fun ⟨drKeyReal,
                    roCache'⟩ _ => ?_)
                  refine evalDist_bind_true_eq_zero_of_support _ _ (fun drKeyRand _ => ?_)
                  cases findHonestPrincipal P hst.base.principals bundle.ikB with
                  | some _ =>
                    simp only [StateT.run_pure, pure_bind]
                    exact hDeadCont _ _ (by unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp
                      [hOpkV, hTgt, hOB, hPowNe])
                  | none =>
                    simp only [StateT.run_pure, pure_bind]
                    exact hDeadCont _ _ (by unfold deadDh4; unfold opkTargetIsV at hOpkV ⊢; simp
                      [hOpkV, hTgt, hOB, hPowNe])
        ·
          have hTgtF : (initSessionSlotIdx sid == sIdx) = false := Bool.eq_false_iff.mpr hTgt
          simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_self, bind_assoc, pure_bind]
          refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ekASk hEk => ?_)
          have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hEk
          refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
          by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
               bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM
                 bundle.pqspkB) bundle.pqspkSig)) = true
          · simp only [hSig, ↓reduceIte, StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
          · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
            cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              dsimp only
              let ekAPk := P.x25519Base ekASk
              let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
              let dh2 := P.x25519 ekASk bundle.ikB
              let dh3 := P.x25519 ekASk bundle.spkB
              let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
              let spkSk := lookupSpkSkTake S P hst.base.spkBundles st.advKeyPows bundle.spkB
              let pos1 := computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk
                bundle.spkB
              let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
              let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
              let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_,
                opkPk) => ([], opkPk)))
              have hPos1 : FgPosRightRep P vSk pos1 dh1 := by
                dsimp only [pos1, dh1]
                rw [computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 spkSk uEntry.ikAPk
                  bundle.spkB huSkLen]
                exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec1 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos2 : FgPosLeftRep P uSk pos2 dh2 := by
                dsimp only [pos2, dh2]
                rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.ikB hEkLen]
                exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec2 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos3 : FgPosLeftRep P uSk pos3 dh3 := by
                dsimp only [pos3, dh3]
                rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.spkB hEkLen]
                exact (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk).sec3 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos4 : FgOptRightRep P vSk pos4? dh4? :=
                computeOptPosPure_left_len32_fgOptRightRep P hP.toWellFormedPrimitivesδ vSk ekASk
                  ekAPk hEkLen bundle.opkB?
              have hSsLen : ss.length = 32 :=
                (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _ hEnc).1
              have hTup : FgTupleRel (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) pos1 pos2 pos3
                pos4? dh1 dh2 dh3 dh4? ss :=
                ⟨hPos1, hPos2, hPos3, hPos4, hSsLen⟩
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind]
              rcases fgPatchPure_eq_or_sample (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) hCache
                hTup with
                ⟨drKeyReal, hEval, hFg⟩ | ⟨hEval, hFg, hStepCache⟩
              · rw [hEval, hFg]
                simp only [pure_bind]
                rw [chooseInitPartnerDrKeyRand_eq_pure P hst.base.respSessions _ _ hRespLen]
                refine evalDist_bind_true_mono_of_support (chooseInitPartnerDrKeyRandPure P
                  hst.base.respSessions _) _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals bundle.ikB with
                | some _ =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont (.hdrResp _)
                  · unfold deadDh4 opkTargetIsV; dsimp only [List.find?]; rw [hTgtF]; exact hDead
                  · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                      ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                        hOpkV, hPrins, hSpks, hOpks, ?_⟩
                    · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg, eraseSessionEntryFg,
                        beq_eq_false_iff_ne.mp hTgtF, hProvEq]
                    · intro s hs
                      rcases List.mem_cons.mp hs with rfl | hMem
                      · exact ⟨hEkLen, rfl, fun h => by rw [hTgtF] at h; cases h⟩
                      · exact hSess s hMem
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont (.initUnfreshResp drKeyReal _)
                  · unfold deadDh4 opkTargetIsV; dsimp only [List.find?]; rw [hTgtF]; exact hDead
                  · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
                      ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                        hOpkV, hPrins, hSpks, hOpks, ?_⟩
                    · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg, eraseSessionEntryFg,
                        beq_eq_false_iff_ne.mp hTgtF, hProvEq]
                    · intro s hs
                      rcases List.mem_cons.mp hs with rfl | hMem
                      · exact ⟨hEkLen, rfl, fun h => by rw [hTgtF] at h; cases h⟩
                      · exact hSess s hMem
              · rw [hEval, hFg]
                simp only [bind_assoc, pure_bind]
                refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun drKeyReal _ => ?_)
                have hCacheNew := hStepCache drKeyReal (by omega)
                rw [chooseInitPartnerDrKeyRand_eq_pure P hst.base.respSessions _ _ hRespLen]
                refine evalDist_bind_true_mono_of_support (chooseInitPartnerDrKeyRandPure P
                  hst.base.respSessions _) _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals bundle.ikB with
                | some _ =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont (.hdrResp _)
                  · unfold deadDh4 opkTargetIsV; dsimp only [List.find?]; rw [hTgtF]; exact hDead
                  · refine ⟨?_, hAdvEq, hCacheNew, by dsimp [List.length_cons]; omega,
                      by dsimp; omega,
                      ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                        hOpkV, hPrins, hSpks, hOpks, ?_⟩
                    · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg, eraseSessionEntryFg,
                        beq_eq_false_iff_ne.mp hTgtF, hProvEq]
                    · intro s hs
                      rcases List.mem_cons.mp hs with rfl | hMem
                      · exact ⟨hEkLen, rfl, fun h => by rw [hTgtF] at h; cases h⟩
                      · exact hSess s hMem
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  apply hCont (.initUnfreshResp drKeyReal _)
                  · unfold deadDh4 opkTargetIsV; dsimp only [List.find?]; rw [hTgtF]; exact hDead
                  · refine ⟨?_, hAdvEq, hCacheNew, by dsimp [List.length_cons]; omega,
                      by dsimp; omega,
                      ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                        hOpkV, hPrins, hSpks, hOpks, ?_⟩
                    · rw [hBaseEq]; simp [eraseStateFgOpk, eraseSessionsFg, eraseSessionEntryFg,
                        beq_eq_false_iff_ne.mp hTgtF, hProvEq]
                    · intro s hs
                      rcases List.mem_cons.mp hs with rfl | hMem
                      · exact ⟨hEkLen, rfl, fun h => by rw [hTgtF] at h; cases h⟩
                      · exact hSess s hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh4 (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh4 P sIdx oIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImplOpk sIdx oIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true} ≤
      𝒟[(fgKeyIndSimImplOpk P P.isValidDhTriple sIdx oIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  rw [fgKeyIndSimImplOpk_run]
  cases q with
  | initPrin u =>
    exact fgStepCoupling_dh4_initPrin S b P hP sIdx oIdx uSk vSk huSk hvSk u rem hst st hDead hInv
      k1 k2 hCont
  | corruptIK u =>
    exact fgStepCoupling_dh4_corruptIK S b P hP sIdx oIdx uSk vSk huSk hvSk u rem hst st hDead
      hInv k1 k2 hCont
  | genSPK u j =>
    exact fgStepCoupling_dh4_genSPK S b P hP sIdx oIdx uSk vSk huSk hvSk u j rem hst st hDead hInv
      k1 k2 hCont
  | genOPK u j o =>
    exact fgStepCoupling_dh4_genOPK S b P hP sIdx oIdx uSk vSk huSk hvSk u j o rem hst st hDead
      hInv k1 k2 hCont
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImplOpk pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPureOpk
      fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh4_initiate S b P hP sIdx oIdx uSk vSk huSk hvSk (.sendOPK u i)
        trivial u bundle rem hst st hDead hInv k1 k2 hCont hDeadCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImplOpk pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPureOpk
      fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh4_initiate S b P hP sIdx oIdx uSk vSk huSk hvSk (.sendNoOPK u i)
        trivial u bundle rem hst st hDead hInv k1 k2 hCont hDeadCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | acceptOPK k j o hdr =>
    exact fgStepCoupling_dh4_acceptOPK S b P hP sIdx oIdx uSk vSk huSk hvSk k j o hdr rem hst st
      hDead hInv k1 k2 hCont
  | acceptNoOPK k j l hdr =>
    exact fgStepCoupling_dh4_acceptNoOPK S b P hP sIdx oIdx uSk vSk huSk hvSk k j l hdr rem hst st
      hDead hInv k1 k2 hCont
  | testSession sid =>
    exact fgStepCoupling_dh4_testSession S b P hP sIdx oIdx uSk vSk huSk hvSk sid rem hst st hDead
      hInv k1 k2 hCont
  | revealSessionKey sid =>
    exact fgStepCoupling_dh4_revealSessionKey S b P hP sIdx oIdx uSk vSk huSk hvSk sid rem hst st
      hDead hInv k1 k2 hCont
  | roQuery secrets =>
    exact fgStepCoupling_dh4_roQuery S b P hP sIdx oIdx uSk vSk huSk hvSk secrets rem hst st hDead
      hInv k1 k2 hCont
  | revealDhSecrets =>
    exact fgStepCoupling_dh4_revealDhSecrets S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
      hInv k1 k2 hCont
  | registerKey sk =>
    exact fgStepCoupling_dh4_registerKey S b P hP sIdx oIdx uSk vSk huSk hvSk sk rem hst st hDead
      hInv k1 k2 hCont
  | revealSpkSk u j =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hOpkV, hPrins, hSpks,
      hOpks, hSess⟩
    have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
    unfold pqxdhKeyIndFgPreImplOpk pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl
      liftFgBase fgKeyIndStepPureOpk fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkEq, bind_assoc, pure_bind]
    cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh4_unchanged S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some kb =>
      rcases kb with ⟨_, bEntry⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      apply hCont (.spkSkResp bEntry.spkSk)
      · rw [deadDh4_eq_of_opk_sess P sIdx oIdx _ rfl rfl]; exact hDead
      · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
          ⟨hValidEc.1, (validSpkBundles_map_revealed S P (u.val,
            j.val) hst.base.spkBundles hValidEc.2.1).1, hValidEc.2.2⟩,
          hOpkV, hPrins, ?_, hOpks, hSess⟩
        intro kv hkv
        rcases List.mem_map.mp hkv with ⟨⟨idx, b0⟩, hMem0, hEq0⟩
        have h0 := hSpks (idx, b0) hMem0
        by_cases hIdx : idx == (u.val, j.val) <;>
          simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq0 <;>
          (subst hEq0; exact h0)

/-- Bounds the Case D (`DH4 = CDH(ek_U*, opk_V*)`) bad-event probability at `(sIdx, oIdx)` by the
    `GapDH` advantage of `fgKeyIndGapDhAdvAtOpk sIdx oIdx S b A`. -/
theorem prob_badKeyIndFgDh4At_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (oIdx : ℕ) (_hoIdx : oIdx ∈ Finset.range S.N_opk_tot) :
    (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
        pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAtOpk sIdx oIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx
  unfold GapDH
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim_eq_preSample_dh4 sIdx oIdx P A.1
    (fun x => pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhExp_fgKeyIndGapDhAdvAtOpk_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh4 P sIdx oIdx (P.x25519Base vSk))
    (FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huLen hvLen)
    (pqxdhKeyIndFgPreImplOpk sIdx oIdx (some uSk) (some vSk) S P)
    (fgKeyIndSimImplOpk P P.isValidDhTriple sIdx oIdx S b.q_total (P.x25519Base uSk) (P.x25519Base
      vSk))
    (fun q s1 hD x hx => pqxdhKeyIndFgPreImplOpk_preserves_deadDh4 P sIdx oIdx hsLt uSk vSk q s1
      hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh4 S b P hP sIdx oIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2 hCont
        hDeadCont)
    (fun x => pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdh4FromAdvRoLog P.isValidDhTriple b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.advRoLog) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD => by simp [badKeyIndFgDh4At_eq_false_of_deadDh4 P b.q_ro sIdx oIdx (P.x25519Base
      vSk) s1 hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh4_terminal_le S b P hP b.q_ro sIdx oIdx uSk vSk huLen hvLen a rem s1 s2 hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyIndSimState.empty S secb)
    (fgSimInvDh4_empty S b P hP sIdx oIdx uSk vSk huLen hvLen secb)

end Proofs.SignalPqxdh.Security.FgGapDh.Opk
