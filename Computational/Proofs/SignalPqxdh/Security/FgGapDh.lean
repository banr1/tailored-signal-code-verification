/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhF
import VCVio.EvalDist.Monad.Basic

@[expose] public section

/-!
# Fiedler–Günther Cases A and C: `GapDH` Bounds

Step-by-step coupling between the pre-sampled Case A game and the `GapDH` simulator, bounding the
Fiedler–Günther `KeyInd` bad event by `GapDH` advantage.
-/

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh

theorem fgStepCoupling_dh1_corruptIK (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh1 uIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hBaseEq]; exact find?_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinFind, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    dsimp only [Option.map]
    simp only [StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1
      k2 hCont
  | some p =>
    rcases p with ⟨u0, entry⟩
    dsimp only [Option.map]
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    have hu0 : u0 = u.val := beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) =>
      x.1 == u.val) hF)
    by_cases hTgt : (u.val == uIdx) = true
    · have hDead' : deadDh1 uIdx { hst with base := { hst.base with
          principals := hst.base.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) } } = true :=
        deadDh1_map_corrupted_eq_true_of_eq uIdx u.val hTgt hst u0 entry hF
      rw [hDeadCont _ _ hDead']
      exact zero_le
    · have hTgtF : (u.val == uIdx) = false := Bool.eq_false_iff.mpr hTgt
      have hu0F : (u0 == uIdx) = false := by rw [hu0]; exact hTgtF
      have hEraseEq : erasePrincipalEntryFg uIdx u0 entry = entry := by
        unfold erasePrincipalEntryFg; simp [hu0F]
      rw [hEraseEq]
      apply hCont (.corrResp entry.secIKA0 entry.secIKAsign)
      · rw [deadDh1_map_corrupted_of_ne uIdx u.val hTgtF hst]
        exact hDead
      · refine ⟨?_, hAdvEq, hCache,
        by dsimp; omega, by dsimp; omega, ?_, hSpkV, ?_, hSpks, hOpks, hSess⟩
        · rw [hBaseEq]
          dsimp [eraseStateFg]
          rw [corrupt_map_erasePrincipalsFg]
        · exact ⟨(validPrincipals_map_corrupted S P u.val hst.base.principals hValidEc.1).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
        · intro kv hkv
          rw [List.mem_map] at hkv
          rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
          have hPr := hPrins (idx, e) heMem
          by_cases hIdx : idx == u.val <;> simp only [hIdx, ↓reduceIte,
            Bool.false_eq_true] at hEq <;>
            (subst hEq; exact hPr)

theorem fgStepCoupling_dh1_genOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.genOPK u j o)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genOPK u j o) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := by rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpkEq, bind_assoc, pure_bind]
  cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun opkSk hOpk => ?_)
    have hLen : opkSk.length = 32 := length_of_mem_support_sampleScalar32 hOpk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false }
    apply hCont (.pkResp (P.x25519Base opkSk))
    · rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache,
      by dsimp; omega, by dsimp; omega, ?_, hSpkV, hPrins, hSpks, ?_, hSess⟩
      · exact ⟨hValidEc.1, hValidEc.2.1,
          (validOpkEntries_cons S u j o oEntry hst.base.opkEntries hValidEc.2.2.1 hAny).1,
          hValidEc.2.2.2⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen, rfl⟩
        · exact hOpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1
      k2 hCont

theorem fgStepCoupling_dh1_genSPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hBaseEq]; exact find?_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  have hSpkAnyEq : st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) =
      hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) := by
    rw [hBaseEq]; exact any_idx_eraseSpkBundlesFg S bIdx (u.val, j.val) hst.base.spkBundles
  unfold pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkAnyEq, hPrinFind, bind_assoc,
    pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp
        k1 k2 hCont
    | some p =>
      rcases p with ⟨u0, uEntry⟩
      dsimp only [Option.map]
      simp only [erasePrincipalEntryFg_secIKAsign, erasePrincipalEntryFg_ikAPk]
      by_cases hTgt : (spkBundleFlatIdx S u j == bIdx) = true
      · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, sampleKemKeyGen, bind_assoc, pure_bind,
          evalDist_sampleScalar32_const]
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        let spkPk := P.x25519Base vSk
        let pqspkPk := (P.kemKeyGen seedKem).1
        let pqspkSk := (P.kemKeyGen seedKem).2
        let bEntry1 : SpkBundleEntry := {
          spkSk := vSk, spkPk := spkPk,
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        let bundleOut : PreKeyBundleInput := {
          ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
          spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
          pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
        have hTgtVal : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = true := hTgt
        have hSpkV' : spkTargetIsV bIdx (P.x25519Base vSk)
            { hst with base :=
              { hst.base with spkBundles :=
              ((u.val, j.val), bEntry1) :: hst.base.spkBundles } } = true := by
          unfold spkTargetIsV at hSpkV ⊢
          simp [List.all_cons, bEntry1, spkPk, hSpkV]
        apply hCont (.bundleResp bundleOut)
        · rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead
        · refine ⟨?_, hAdvEq, hCache,
          by dsimp; omega, by dsimp; omega, ?_, hSpkV', hPrins, ?_, hOpks, hSess⟩
          · rw [hBaseEq]
            simp [eraseStateFg, eraseSpkBundlesFg, eraseSpkBundleEntryFg, beq_iff_eq.mp hTgtVal]
          · exact ⟨hValidEc.1,
              (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
              hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hvSk, rfl, fun _ => rfl⟩
            · exact hSpks kv hMem
      · have hTgtF : (spkBundleFlatIdx S u j == bIdx) = false := Bool.eq_false_iff.mpr hTgt
        have hTgtValF : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := hTgtF
        simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, sampleKemKeyGen, bind_assoc, pure_bind]
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
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        let bundleOut : PreKeyBundleInput := {
          ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
          spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
          pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
        have hSpkV' : spkTargetIsV bIdx (P.x25519Base vSk)
            { hst with base :=
              { hst.base with spkBundles :=
              ((u.val, j.val), bEntry1) :: hst.base.spkBundles } } = true := by
          unfold spkTargetIsV at hSpkV ⊢
          simp [List.all_cons, hTgtValF, hSpkV]
        apply hCont (.bundleResp bundleOut)
        · rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead
        · refine ⟨?_, hAdvEq, hCache,
          by dsimp; omega, by dsimp; omega, ?_, hSpkV', hPrins, ?_, hOpks, hSess⟩
          · rw [hBaseEq]
            simp [eraseStateFg, eraseSpkBundlesFg, eraseSpkBundleEntryFg,
              beq_eq_false_iff_ne.mp hTgtValF]
          · exact ⟨hValidEc.1,
              (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
              hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hSpkLen, rfl, fun h => by rw [hTgtValF] at h; cases h⟩
            · exact hSpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1
      k2 hCont

theorem fgStepCoupling_dh1_roQuery (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (secrets : Bytes) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.roQuery secrets)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roQuery secrets) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  refine fgRoQuery_coupling R hCache hFgLen (fun dk roCache' rawRoCache' fgL' hCache' hFgLen' => ?_)
  apply hCont (.drKeyResp dk)
  · rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead
  · exact ⟨hBaseEq, ⟨by dsimp; rw [hAdvEq.1], hAdvEq.2⟩, hCache', hFgLen',
      by dsimp [List.length_cons]; omega, hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩

theorem fgStepCoupling_dh1_revealDhSecrets (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P .revealDhSecrets).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) .revealDhSecrets st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, ↓reduceIte,
    StateT.run_pure, pure_bind]
  exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv .noneResp k1 k2
    hCont

theorem fgStepCoupling_dh1_testSession (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.testSession sid)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.testSession sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  refine fgTestSession_coupling id
    (by rw [hBaseEq]; exact isFreshKeyIndSession_eraseStateFg true uIdx bIdx hst.base sid)
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl)
    (by rw [hBaseEq]; exact Option.map_id'.symm)
    (fun _ => rfl) (fun _ => rfl)
    (fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1 k2
      hCont)
    (fun r => hCont r _ _ (by rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
       validKeyIndEc_map_tested sid hValidEc, hSpkV, hPrins, hSpks, hOpks, fun s hs => by
         rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
         cases s0.sid == sid <;> exact hSess s0 hs0⟩)
    (fun r => hCont r _ _ (by rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
       validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hSpkV, hPrins, hSpks, hOpks, hSess⟩)

theorem fgStepCoupling_dh1_revealSessionKey (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.revealSessionKey sid)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.revealSessionKey sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  refine fgRevealSessionKey_coupling id
    (by rw [hBaseEq]; rfl)
    (by rw [hBaseEq]; exact Option.map_id'.symm)
    (fun _ => rfl) (fun _ => rfl)
    (fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1 k2
      hCont)
    (fun r => hCont r _ _ (by rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
       validKeyIndEc_map_revealed sid hValidEc, hSpkV, hPrins, hSpks, hOpks, fun s hs => by
         rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
         cases s0.sid == sid <;> exact hSess s0 hs0⟩)
    (fun r => hCont r _ _ (by rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
       validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hSpkV, hPrins, hSpks, hOpks, hSess⟩)

theorem fgStepCoupling_dh1_acceptNoOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk (rem +
      1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.acceptNoOPK k j l hdr)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.acceptNoOPK k j l hdr) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hTakePrin : st.base.principals.take S.N_dh = erasePrincipalsFg uIdx hst.base.principals := by
    rw [hBaseEq]; exact List.take_of_length_le (by dsimp [eraseStateFg]; rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk := by
    rw [hBaseEq]
    exact koskSenderOkTake_erasePrincipalsFg_eq S P uIdx hst.base.principals st.advKeyPows
      hst.base.advKeys hdr.ikAPk hLengths.1 hAdvEq.2.1
  refine fgAcceptNoOPK_coupling R hP (erasePrincipalEntryFg uIdx) (eraseSpkBundleEntryFg S bIdx)
    hCache hFgLen hValidEc hAdvEq (fun kv hkv => ⟨(hPrins kv hkv).1, (hPrins kv hkv).2.1⟩)
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) hKoskEq
    (by rw [hBaseEq]; exact find?_idx_erasePrincipalsFg uIdx k.val hst.base.principals)
    (by rw [hBaseEq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val) hst.base.spkBundles)
    (erasePrincipalEntryFg_ikAPk uIdx) (eraseSpkBundleEntryFg_pqspkSk S bIdx)
    (eraseSpkBundleEntryFg_spkPk S bIdx) (eraseSpkBundleEntryFg_pqspkPk S bIdx)
    (by
      rw [hTakePrin]
      exact findHonestPrincipal_erasePrincipalsFg_isSome P uIdx hst.base.principals hdr.ikAPk)
    (fun rInit => by rw [hBaseEq]; rfl)
    (fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1 k2
      hCont)
    (fun k0 kEntry kb0 bEntry hkMem hbMem hIkOnCurve hEkOnCurve =>
      ⟨computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
          hdr.ikAPk (hSpks (kb0, bEntry) hbMem) hIkOnCurve,
        computeTwoSideOrPairPosPure_erasePrin_fgPosRightRep P hP uIdx uSk k0 kEntry
          hdr.ekAPk (hPrins (k0, kEntry) hkMem) hEkOnCurve,
        computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
          hdr.ekAPk (hSpks (kb0, bEntry) hbMem) hEkOnCurve⟩)
    (fun r rEntry roCache' fgL' hValidEc' hCache' hFgLen' =>
      hCont r _ _ (by rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead)
        ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache', hFgLen', by dsimp; omega,
          hValidEc', hSpkV, hPrins, hSpks, hOpks, hSess⟩)

theorem fgStepCoupling_dh1_acceptOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk (rem +
      1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.acceptOPK k j o hdr)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.acceptOPK k j o hdr) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hTakePrin : st.base.principals.take S.N_dh = erasePrincipalsFg uIdx hst.base.principals := by
    rw [hBaseEq]; exact List.take_of_length_le (by dsimp [eraseStateFg]; rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk := by
    rw [hBaseEq]
    exact koskSenderOkTake_erasePrincipalsFg_eq S P uIdx hst.base.principals st.advKeyPows
      hst.base.advKeys hdr.ikAPk hLengths.1 hAdvEq.2.1
  refine fgAcceptOPK_coupling R hP (erasePrincipalEntryFg uIdx) (eraseSpkBundleEntryFg S bIdx)
    hCache hFgLen hValidEc hAdvEq (fun kv hkv => ⟨(hPrins kv hkv).1, (hPrins kv hkv).2.1⟩) hOpks
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) hKoskEq
    (by rw [hBaseEq]; exact find?_idx_erasePrincipalsFg uIdx k.val hst.base.principals)
    (by rw [hBaseEq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val) hst.base.spkBundles)
    (erasePrincipalEntryFg_ikAPk uIdx) (eraseSpkBundleEntryFg_pqspkSk S bIdx)
    (eraseSpkBundleEntryFg_spkPk S bIdx) (eraseSpkBundleEntryFg_pqspkPk S bIdx)
    (by
      rw [hTakePrin]
      exact findHonestPrincipal_erasePrincipalsFg_isSome P uIdx hst.base.principals hdr.ikAPk)
    (fun rInit => by rw [hBaseEq]; rfl)
    (fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1 k2
      hCont)
    (fun k0 kEntry kb0 bEntry hkMem hbMem hIkOnCurve hEkOnCurve =>
      ⟨computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
          hdr.ikAPk (hSpks (kb0, bEntry) hbMem) hIkOnCurve,
        computeTwoSideOrPairPosPure_erasePrin_fgPosRightRep P hP uIdx uSk k0 kEntry
          hdr.ekAPk (hPrins (k0, kEntry) hkMem) hEkOnCurve,
        computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
          hdr.ekAPk (hSpks (kb0, bEntry) hbMem) hEkOnCurve⟩)
    (fun r rEntry roCache' fgL' hValidEc' hOpks' hCache' hFgLen' =>
      hCont r _ _ (by rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead)
        ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache', hFgLen', by dsimp; omega,
          hValidEc', hSpkV, hPrins, hSpks, hOpks', hSess⟩)

theorem find?_spkPk_eraseSpkBundlesFg (P : Primitives) (S : Setup) (bIdx : ℕ) (pk : Bytes)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx spkBundles).find? (fun (_, b) => P.pow8 b.spkPk == P.pow8 pk) =
      (spkBundles.find? (fun (_, b) => P.pow8 b.spkPk == P.pow8 pk)).map
        (fun (k, b) => (k, eraseSpkBundleEntryFg S bIdx k b)) := by
  simp [eraseSpkBundlesFg, List.find?_map]

theorem lookupSpkSkTake_eraseSpk_dichotomy
    (S : Setup) (P : Primitives) (bIdx : ℕ) (vSk : Bytes)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows advKeys : List (Bytes × Bytes)) (pk : Bytes)
    (hSpks : ∀ kv ∈ spkBundles,
      kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
      ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = vSk))
    (hS : spkBundles.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk') => (sk, P.pow8 pk')))
    (hAdvSkLen : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hSpkReg : (isGameSpk P spkBundles pk || isAdvRegistered P advKeys pk) = true) :
    let spkBSk := lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows pk
    (spkBSk = [] ∧ vSk.length = 32 ∧ P.pow8 pk = P.pow8 (P.x25519Base vSk)) ∨
    (spkBSk.length = 32 ∧ P.pow8 pk = P.pow8 (P.x25519Base spkBSk)) := by
  dsimp only
  have hS' : (eraseSpkBundlesFg S bIdx spkBundles).length ≤ S.N_dh := by
    rw [eraseSpkBundlesFg_length]; exact hS
  unfold lookupSpkSkTake
  dsimp only
  rw [List.take_of_length_le hS', find?_spkPk_eraseSpkBundlesFg]
  cases hFB : spkBundles.find? (fun (_, b) => P.pow8 b.spkPk == P.pow8 pk) with
  | some kb =>
    rcases kb with ⟨k, bEntry⟩
    dsimp only [Option.map]
    have hbMem := List.mem_of_find?_eq_some hFB
    have hbPow : P.pow8 bEntry.spkPk = P.pow8 pk :=
      beq_iff_eq.mp (List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
        P.pow8 x.2.spkPk == P.pow8 pk) hFB)
    rcases hSpks (k, bEntry) hbMem with ⟨hbLen, hbPk, hbTgt⟩
    dsimp only [eraseSpkBundleEntryFg]
    by_cases hB : (spkBundleFlatIdxVal S k == bIdx) = true
    · simp only [hB, ↓reduceIte]
      left
      exact ⟨trivial, hbTgt hB ▸ hbLen, by rw [← hbPow, hbPk, hbTgt hB]⟩
    · have hBF : (spkBundleFlatIdxVal S k == bIdx) = false := Bool.eq_false_iff.mpr hB
      simp only [hBF, Bool.false_eq_true, ↓reduceIte]
      right
      exact ⟨hbLen, by rw [← hbPow, hbPk]⟩
  | none =>
    dsimp only [Option.map]
    have hGameSpkF : isGameSpk P spkBundles pk = false := by
      unfold isGameSpk
      cases hAny : spkBundles.any (fun (_, b) => P.pow8 b.spkPk == P.pow8 pk)
      · rfl
      · rcases List.any_eq_true.mp hAny with ⟨x, hxMem, hxPred⟩
        exact False.elim (List.find?_eq_none.mp hFB x hxMem hxPred)
    rw [hGameSpkF, Bool.false_or] at hSpkReg
    have hAdvPowsReg : isAdvRegisteredPows advKeyPows (P.pow8 pk) = true := by
      rw [hAdvPows, isAdvRegisteredPows_map_eq]; exact hSpkReg
    unfold isAdvRegisteredPows at hAdvPowsReg
    cases hFA : advKeyPows.find? (fun (_, wPk) => wPk == P.pow8 pk) with
    | none =>
      rcases List.any_eq_true.mp hAdvPowsReg with ⟨x, hxMem, hxPred⟩
      exact False.elim (List.find?_eq_none.mp hFA x hxMem hxPred)
    | some sp =>
      rcases sp with ⟨sk, wPk⟩
      dsimp only
      have hspMem := List.mem_of_find?_eq_some hFA
      have hPowEq : wPk = P.pow8 pk :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : Bytes × Bytes) => x.2 == P.pow8 pk) hFA)
      rw [hAdvPows, List.mem_map] at hspMem
      rcases hspMem with ⟨⟨sk0, pk0⟩, hkvMem, hPairEq⟩
      injection hPairEq with hskEq hpow0Eq
      subst hskEq
      rcases hAdvSkLen (sk0, pk0) hkvMem with ⟨hLen0, hPk0⟩
      dsimp only at hLen0 hPk0
      right
      exact ⟨hLen0, by rw [← hPowEq, ← hpow0Eq, hPk0]⟩

theorem computeTwoSideOrPairPosPure_erasePrin_lookupSpkSkTake_fgPosRightRep
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (u : Nat) (uEntry : PrincipalEntry) (pk : Bytes)
    (hu : uEntry.secIKA0.length = 32 ∧ uEntry.ikAPk = P.x25519Base uEntry.secIKA0 ∧
      ((u == uIdx) = true → uEntry.secIKA0 = uSk))
    (hSpks : ∀ kv ∈ spkBundles,
      kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
      ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = vSk))
    (hS : spkBundles.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk') => (sk, P.pow8 pk')))
    (hAdvSkLen : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hSpkReg : (isGameSpk P spkBundles pk || isAdvRegistered P advKeys pk) = true) :
    FgPosRightRep P vSk
      (computeTwoSideOrPairPosPure P (erasePrincipalEntryFg uIdx u uEntry).secIKA0
        (lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows pk)
        uEntry.ikAPk pk)
      (P.x25519 uEntry.secIKA0 pk) := by
  dsimp only [erasePrincipalEntryFg]
  by_cases hIdx : (u == uIdx) = true
  · have hSk : uEntry.secIKA0 = uSk := hu.2.2 hIdx
    have hPk : uEntry.ikAPk = P.x25519Base uSk := by rw [hu.2.1, hSk]
    simp only [hIdx, ↓reduceIte, hPk, hSk]
    rcases lookupSpkSkTake_eraseSpk_dichotomy S P bIdx vSk spkBundles advKeyPows advKeys pk
      hSpks hS hAdvPows hAdvSkLen hSpkReg with ⟨hEmpty, hvLen, hPow⟩ | ⟨hLen, hPow⟩
    · rw [hEmpty, computeTwoSideOrPairPosPure_nil_nil]
      exact fgPosRightRep_mkPair_left_of_pow8 P hP.toWellFormedPrimitivesδ uSk vSk pk (hSk ▸ hu.1)
        hvLen (hP.pow8_base_len pk vSk hPow) hPow
    · rw [computeTwoSideOrPairPosPure_nil_right_len32 P _ (P.x25519Base uSk) pk hLen]
      have hDhEq : P.x25519 (lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows
          pk) (P.x25519Base uSk) =
          P.x25519 uSk pk := by
        rw [← hP.toWellFormedPrimitivesδ.x25519_comm uSk,
            ← hP.toWellFormedPrimitivesδ.x25519_pow8_congr uSk pk _
                (hP.pow8_base_len pk _ hPow) (hP.x25519Base_len _) hPow]
      rw [hDhEq]
      exact fgPosRightRep_mkSecret P vSk _ (hP.x25519_len _ _)
  · have hIdxF : (u == uIdx) = false := Bool.eq_false_iff.mpr hIdx
    simp only [hIdxF, Bool.false_eq_true, ↓reduceIte,
      computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 _ uEntry.ikAPk pk hu.1]
    exact fgPosRightRep_mkSecret P vSk _ (hP.x25519_len _ _)

theorem initDh1Cand_eq_of_ne_target (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (bIdx : ℕ) (vSk : Bytes)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (s : KeyIndInitiatorEntry S) (uSk2 : Bytes)
    (_huSk2 : uSk2.length = 32)
    (hIk : s.hdr.ikAPk = P.x25519Base uSk2)
    (hSpks : ∀ kv ∈ spkBundles,
      kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
      ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = vSk))
    (hS : spkBundles.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk') => (sk, P.pow8 pk')))
    (hAdvSkLen : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hSpkReg : (isGameSpk P spkBundles s.peerSpkPk || isAdvRegistered P advKeys s.peerSpkPk) = true)
    (hNeV : P.pow8 s.peerSpkPk ≠ P.pow8 (P.x25519Base vSk)) :
    initDh1Cand S P (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows s =
      P.x25519 uSk2 s.peerSpkPk := by
  unfold initDh1Cand
  rcases lookupSpkSkTake_eraseSpk_dichotomy S P bIdx vSk spkBundles advKeyPows advKeys s.peerSpkPk
    hSpks hS hAdvPows hAdvSkLen hSpkReg with ⟨_, _, hPow⟩ | ⟨hLen, hPow⟩
  · exfalso; exact hNeV hPow
  · rw [hIk, ← hP.toWellFormedPrimitivesδ.x25519_comm uSk2,
        ← hP.toWellFormedPrimitivesδ.x25519_pow8_congr uSk2 s.peerSpkPk _
            (hP.pow8_base_len s.peerSpkPk _ hPow) (hP.x25519Base_len _) hPow]

theorem respDh1Cand_eq_of_ne_target (S : Setup) (P : Primitives) (bIdx : ℕ)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (r : KeyIndRespEntry S) (k2 : Nat × Nat) (b2 : SpkBundleEntry)
    (hS : spkBundles.length ≤ S.N_dh)
    (hFind : spkBundles.find? (fun (idx, _) => idx == respBundleKey r.sid) = some (k2, b2))
    (hNeB : (spkBundleFlatIdxVal S k2 == bIdx) = false) :
    respDh1Cand S P (eraseSpkBundlesFg S bIdx spkBundles) r =
      P.x25519 b2.spkSk r.hdr.ikAPk := by
  unfold respDh1Cand
  have hTake : (eraseSpkBundlesFg S bIdx spkBundles).take S.N_dh =
      eraseSpkBundlesFg S bIdx spkBundles :=
    List.take_of_length_le (by rw [eraseSpkBundlesFg_length]; exact hS)
  have hNeB' : spkBundleFlatIdxVal S k2 ≠ bIdx := by
    intro h; exact Bool.false_ne_true (hNeB ▸ beq_iff_eq.mpr h)
  rw [hTake, find?_idx_eraseSpkBundlesFg S bIdx (respBundleKey r.sid) spkBundles, hFind]
  simp [eraseSpkBundleEntryFg, hNeB']

theorem fgStepCoupling_dh1_initiate (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk (rem +
      1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(do
        let x ← (fgPreInitiate true uIdx (some uSk) S P sid u bundle).run hst.base
        k1 (x.1, { base := x.2, advRoLog := hst.advRoLog }))] {true} ≤
      𝒟[fgRunInitiatePure P P.isValidDhTriple true uIdx S b.q_total
          (P.x25519Base uSk) sid u bundle st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hRespLen := validKeyIndEc_resp_length_le_fg S hst.base hValidEc
  have hAnyEq : st.base.sessions.any (fun e => e.sid == sid) =
      hst.base.sessions.any (fun e => e.sid == sid) := by
    rw [hBaseEq]; rfl
  have hPrinEq : st.base.principals = erasePrincipalsFg uIdx hst.base.principals :=
    by rw [hBaseEq]; rfl
  have hSpkEq : st.base.spkBundles = eraseSpkBundlesFg S bIdx hst.base.spkBundles :=
    by rw [hBaseEq]; rfl
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := by rw [hBaseEq]; rfl
  have hRespEq : st.base.respSessions = hst.base.respSessions := by rw [hBaseEq]; rfl
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hBaseEq]; exact find?_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  have hTakePrin : st.base.principals.take S.N_dh = erasePrincipalsFg uIdx hst.base.principals := by
    rw [hPrinEq, List.take_of_length_le (by rw [erasePrincipalsFg_length]; exact hLengths.1)]
  have hKoskEq : koskBundleOkTake S P st.base.principals
        st.base.spkBundles st.base.opkEntries st.advKeyPows bundle =
      koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries hst.base.advKeys
        bundle := by
    rw [hPrinEq, hSpkEq, hOpkEq]
    exact koskBundleOkTake_erasePrin_eraseSpk_eq S P uIdx bIdx
      hst.base.principals hst.base.spkBundles hst.base.opkEntries st.advKeyPows hst.base.advKeys
        bundle
      hLengths.1 hLengths.2.1 hLengths.2.2.1 hAdvEq.2.1
  have hLookupEq : lookupSpkSkTake S P st.base.spkBundles st.advKeyPows bundle.spkB =
      lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx hst.base.spkBundles) st.advKeyPows bundle.spkB
        := by
    rw [hSpkEq]
  have hProvEq : checkBundleProvenanceTake S P (erasePrincipalsFg uIdx hst.base.principals)
        (eraseSpkBundlesFg S bIdx hst.base.spkBundles) hst.base.opkEntries bundle =
      checkBundleProvenance P hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle :=
    checkBundleProvenanceTake_erasePrin_eraseSpk_eq S P uIdx bIdx
      hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle
      hLengths.1 hLengths.2.1 hLengths.2.2.1
  unfold fgPreInitiate fgRunInitiatePure
  simp only [StateT.run_bind, StateT.run_get, hAnyEq, hPrinFind, hRespEq, hTakePrin, hKoskEq,
    hLookupEq,
    resolveSigPk_erasePrincipalsFg, isHonestUncorruptedPeer_erasePrincipalsFg,
    Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases hAny : hst.base.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hAnyMap : ((sessPksKeyInd S hst.base).map Prod.fst).any (fun s => s == sid) = false := by
      simp [sessPksKeyInd, List.any_map, Function.comp_def, hAny]
    have hValidSess' : ValidSessionIds S (sid :: (sessPksKeyInd S hst.base).map Prod.fst) :=
      (validSessionIds_cons S sid ((sessPksKeyInd S hst.base).map Prod.fst) hSend hValidEc.2.2.2.1
        hAnyMap).1
    cases hFU : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp
        k1 k2 hCont
    | some pu =>
      rcases pu with ⟨u0, uEntry⟩
      simp only [Option.map_some]
      have huMem := List.mem_of_find?_eq_some hFU
      rcases hPrins (u0, uEntry) huMem with ⟨huSkLen, huPk, huTgt⟩
      by_cases hKosk : (!koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
        hst.base.advKeys bundle) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0
          .noneResp k1 k2 hCont
      · have hKoskT : koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
          hst.base.advKeys bundle = true :=
          of_not_not_eq_true hKosk
        have hSpkReg : (isGameSpk P hst.base.spkBundles bundle.spkB || isAdvRegistered P
          hst.base.advKeys bundle.spkB) = true := by
          unfold koskBundleOk at hKoskT
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hKoskT).1).2
        simp only [hKosk, Bool.false_eq_true, ↓reduceIte,
          erasePrincipalEntryFg_ikAPk, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind]
        refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ekASk hEk => ?_)
        have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hEk
        refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
        by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
             bundle.spkB) bundle.spkSig &&
             P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
               bundle.pqspkSig)) = true
        · simp only [hSig, ↓reduceIte, StateT.run_pure, pure_bind]
          exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0
            .noneResp k1 k2 hCont
        · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
          cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            simp only [StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0
              .noneResp k1 k2 hCont
          | some sc =>
            rcases sc with ⟨ss, kemCt⟩
            dsimp only
            have hSsLen : ss.length = 32 := (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _ hEnc).1
            let ekAPk := P.x25519Base ekASk
            let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
            let dh2 := P.x25519 ekASk bundle.ikB
            let dh3 := P.x25519 ekASk bundle.spkB
            let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
            let spkSk :=
              lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx hst.base.spkBundles) st.advKeyPows
              bundle.spkB
            let pos1 :=
              computeTwoSideOrPairPosPure P (erasePrincipalEntryFg uIdx u0 uEntry).secIKA0 spkSk
              uEntry.ikAPk bundle.spkB
            let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
            let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
            let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([],
              opkPk)))
            have hPos1 : FgPosRightRep P vSk pos1 dh1 :=
              computeTwoSideOrPairPosPure_erasePrin_lookupSpkSkTake_fgPosRightRep S P hP
                uIdx bIdx uSk vSk hst.base.spkBundles st.advKeyPows hst.base.advKeys
                u0 uEntry bundle.spkB ⟨huSkLen, huPk,
                  huTgt⟩ hSpks hLengths.2.1 hAdvEq.2.1 hAdvEq.2.2 hSpkReg
            have hPos2 : FgPosRightRep P uSk pos2 dh2 := by
              dsimp only [pos2, dh2]
              rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.ikB hEkLen]
              exact R.sec2 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
            have hPos3 : FgPosRightRep P vSk pos3 dh3 := by
              dsimp only [pos3, dh3]
              rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.spkB hEkLen]
              exact R.sec3 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
            have hPos4 : FgOptRightRep P vSk pos4? dh4? :=
              computeOptPosPure_left_len32_fgOptRightRep P hP.toWellFormedPrimitivesδ vSk ekASk ekAPk
                hEkLen bundle.opkB?
            have hTup : FgTupleRel R pos1 pos2 pos3 pos4? dh1 dh2 dh3 dh4? ss :=
              ⟨hPos1, hPos2, hPos3, hPos4, hSsLen⟩
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
              bind_assoc, pure_bind, findHonestPrincipal_erasePrincipalsFg]
            refine fgPatchPure_bind_le R hCache hFgLen hTup
              (fun drKeyReal roCache' fgL' hCache' hFgLen' => ?_)
            rw [chooseInitPartnerDrKeyRand_eq_pure P hst.base.respSessions _ _ hRespLen]
            refine evalDist_bind_true_mono_of_support (chooseInitPartnerDrKeyRandPure P
              hst.base.respSessions _) _ _ (fun drKeyRand _ => ?_)
            cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
              simp only [Option.map, StateT.run_pure, pure_bind]
            all_goals
              apply hCont
              · rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead
              · refine ⟨?_, hAdvEq, hCache', hFgLen', by dsimp; omega,
                  ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                    hSpkV, hPrins, hSpks, hOpks, ?_⟩
                · rw [hBaseEq]; simp [eraseStateFg, hProvEq]
                · intro s hs
                  rcases List.mem_cons.mp hs with rfl | hMem
                  · exact ⟨hEkLen, rfl⟩
                  · exact hSess s hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1
      k2 hCont

theorem fgStepCoupling_dh1 (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDeadFull : deadDh1Full uIdx bIdx hst = false)
    (hInv : FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk (rem +
      1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh1Full uIdx bIdx hst' = false →
      FgSimInvDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadContFull : ∀ r hst', deadDh1Full uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true} ≤
      𝒟[(fgKeyIndSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk
  have hDead : deadDh1 uIdx hst = false :=
    (Bool.or_eq_false_iff.mp hDeadFull).1
  have hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true} := by
    intro r hst' st' hD1 hInv'
    by_cases hRev : spkTargetRevealed bIdx hst' = true
    · rw [hDeadContFull r hst' (by unfold deadDh1Full; simp [hRev])]
      exact zero_le
    · exact hContFull r hst' st' (by unfold deadDh1Full; simp [hD1,
      Bool.eq_false_iff.mpr hRev]) hInv'
  have hDeadCont : ∀ r hst', deadDh1 uIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0 := by
    intro r hst' hD1
    exact hDeadContFull r hst' (by unfold deadDh1Full; simp [hD1])
  have hRhs : (fgKeyIndSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total
      (P.x25519Base uSk) (P.x25519Base vSk) q).run st =
      fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q st := by
    unfold fgKeyIndSimImpl
    simp
  rw [hRhs]
  cases q with
  | initPrin u =>
    exact fgStepCoupling_dh1_initPrin S b P R uIdx bIdx uSk vSk huSk u rem hst st hDead hInv k1 k2
      hCont
  | corruptIK u =>
    exact fgStepCoupling_dh1_corruptIK S b P R uIdx bIdx uSk vSk u rem hst st hDead hInv k1 k2 hCont
      hDeadCont
  | genSPK u j =>
    exact fgStepCoupling_dh1_genSPK S b P R uIdx bIdx uSk vSk hvSk u j rem hst st hDead hInv k1 k2
      hCont
  | genOPK u j o =>
    exact fgStepCoupling_dh1_genOPK S b P R uIdx bIdx uSk vSk u j o rem hst st hDead hInv k1 k2
      hCont
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh1_initiate S b P hP uIdx bIdx uSk vSk huSk hvSk (.sendOPK u i) trivial
        u bundle rem hst st hDead hInv k1 k2 hCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv .noneResp
        k1 k2 hCont
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh1_initiate S b P hP uIdx bIdx uSk vSk huSk hvSk (.sendNoOPK u i)
        trivial u bundle rem hst st hDead hInv k1 k2 hCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv .noneResp
        k1 k2 hCont
  | acceptOPK k j o hdr =>
    exact fgStepCoupling_dh1_acceptOPK S b P hP uIdx bIdx uSk vSk huSk hvSk k j o hdr rem hst st
      hDead hInv k1 k2 hCont
  | acceptNoOPK k j l hdr =>
    exact fgStepCoupling_dh1_acceptNoOPK S b P hP uIdx bIdx uSk vSk huSk hvSk k j l hdr rem hst st
      hDead hInv k1 k2 hCont
  | testSession sid =>
    exact fgStepCoupling_dh1_testSession S b P R uIdx bIdx uSk vSk sid rem hst st hDead hInv k1 k2
      hCont
  | revealSessionKey sid =>
    exact fgStepCoupling_dh1_revealSessionKey S b P R uIdx bIdx uSk vSk sid rem hst st hDead hInv k1
      k2 hCont
  | roQuery secrets =>
    exact fgStepCoupling_dh1_roQuery S b P R uIdx bIdx uSk vSk secrets rem hst st hDead hInv k1 k2
      hCont
  | revealDhSecrets =>
    exact fgStepCoupling_dh1_revealDhSecrets S b P R uIdx bIdx uSk vSk rem hst st hDead hInv k1 k2
      hCont
  | registerKey sk =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
      hOpks, hSess⟩
    exact fgRegisterKey_coupling
      (fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp
        k1 k2 hCont)
      (fun hSkLen32 => hCont _ _ _ (by rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead)
        ⟨by rw [hBaseEq]; rfl, fgAdvEq_registerKey hSkLen32 hAdvEq, hCache,
          by dsimp; omega, by dsimp; omega, validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl,
          hSpkV, hPrins, hSpks, hOpks, hSess⟩)
  | revealSpkSk u j =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
      hOpks, hSess⟩
    have hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) =
        (hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val))).map
          (fun (idx, b) => (idx, eraseSpkBundleEntryFg S bIdx idx b)) := by
      rw [hBaseEq]; exact find?_idx_eraseSpkBundlesFg S bIdx (u.val, j.val) hst.base.spkBundles
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkFind, bind_assoc, pure_bind]
    cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp
        k1 k2 hCont
    | some kb =>
      rcases kb with ⟨k0, bEntry⟩
      dsimp only [Option.map]
      by_cases hTgt : (spkBundleFlatIdx S u j == bIdx) = true
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        have hRevTrue :=
          spkTargetRevealed_map_revealed_of_eq bIdx u j hTgt hst hValidEc.2.1 k0 bEntry hFB
        rw [hDeadContFull (.spkSkResp bEntry.spkSk) _ (Bool.or_eq_true_iff.mpr (Or.inr hRevTrue))]
        exact zero_le
      · have hTgtF : (spkBundleFlatIdx S u j == bIdx) = false := Bool.eq_false_iff.mpr hTgt
        have hk0 : (k0 == (u.val, j.val)) = true :=
          List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) => x.1 == (u.val, j.val)) hFB
        rw [eraseSpkBundleEntryFg_eq_self_of_ne S bIdx u j hTgtF k0 bEntry hk0]
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        apply hCont (.spkSkResp bEntry.spkSk)
        · rw [deadDh1_eq_of_principals uIdx rfl]; exact hDead
        · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
            ⟨hValidEc.1, (validSpkBundles_map_revealed S P (u.val,
              j.val) hst.base.spkBundles hValidEc.2.1).1, hValidEc.2.2⟩,
            by rw [spkTargetIsV_map_revealed]; exact hSpkV, hPrins, ?_, hOpks, hSess⟩
          · rw [hBaseEq]
            dsimp only [eraseStateFg]
            rw [eraseSpkBundlesFg_map_revealed]
          · intro kv hkv
            rcases List.mem_map.mp hkv with ⟨⟨idx, b0⟩, hMem0, hEq0⟩
            have h0 := hSpks (idx, b0) hMem0
            split_ifs at hEq0 <;> subst hEq0 <;> exact h0

/-- Per-slot Case A (`DH1`) bound on `badKeyIndFgDh1At` in `runKeyIndFgSim` against `GapDH`. -/
theorem prob_badKeyIndFgDh1At_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (KeyIndAdversary S) b)
    (uIdx : ℕ) (_huIdx : uIdx ∈ Finset.range S.N_id)
    (bIdx : ℕ) (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
        pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAt true uIdx bIdx S b A) := by
  unfold GapDH
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim_eq_preSample_dh1 uIdx bIdx P A.1
    (fun x => pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhExp_fgKeyIndGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  let R := FgSlotReps.ofDh1 P hP uSk vSk huLen hvLen
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh1Full uIdx bIdx)
    (FgSimInvDh1 S b P R uIdx bIdx uSk vSk)
    (pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P)
    (fgKeyIndSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total (P.x25519Base uSk) (P.x25519Base
      vSk))
    (fun q s1 hD x hx =>
      pqxdhKeyIndFgPreImpl_preserves_deadDh1Full P uIdx bIdx uSk vSk q s1 hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh1 S b P hP uIdx bIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2 hCont
        hDeadCont)
    (fun x => pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdhFromSimState S P P.isValidDhTriple true b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD => by simp [badKeyIndFgDh1At_eq_false_of_deadDh1Full P b.q_ro uIdx bIdx s1 hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh1_terminal_le S b P hP R b.q_ro uIdx bIdx uSk vSk a rem s1 s2 hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyIndSimState.empty S secb)
    (fgSimInvDh1_empty S b P R uIdx bIdx uSk vSk secb)

end Proofs.SignalPqxdh.Security.FgGapDh

namespace SignalPqxdh.Security
export _root_.Proofs.SignalPqxdh.Security.FgGapDh (GdhBounded gapDhDdhImpl gapDhFullImpl fgEntryMatchesPure fgPatchPure pureExtractCdhFromAdvRoLog pureExtractCdhFromAdvRoLog_wins_of_mem gapDhExp_fgKeyIndGapDhAdvAt_eq choosePartnerDrKeyRandPure mkSecretPosPure mkPairPosPure computeTwoSideOrPairPosPure computeOptPosPure fgRoQueryPure fgRunInitiatePure fgRunAcceptOPKPure fgRunAcceptNoOPKPure fgKeyIndStepPure simulateQ_gapDhFullImpl_fgRoQueryGdh simulateQ_gapDhFullImpl_fgRunInitiateGdh simulateQ_gapDhFullImpl_fgRunAcceptOPKGdh simulateQ_gapDhFullImpl_fgRunAcceptNoOPKGdh simulateQ_gapDhFullImpl_fgKeyIndStep RelProbUpToBad simulateQ_relProbUpToBad evalDist_simulateQ_eq_uniformBool_of_bad_preserved evalDist_simulateQ_eq_of_step_or_bad KeyIndFgCutoffState pqxdhKeyIndFgImpl runKeyIndFgSim badKeyIndFgDh1At badKeyIndFgDh3At badKeyIndFgAny prob_or_le_add_fg prob_badKeyIndFgAny_le_sum x25519_eq_iff_pow8_eq ddhEqPure_pair_pair_same_right_iff ddhEqPure_pair_pair_same_left_iff evalDist_simulateQ_preSample_slot_eq_of_hasFired evalDist_simulateQ_preSample_slot_eq evalDist_simulateQ_preSample_slot_eq_c0 initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt spkBundleFlatIdx_inj hasFiredSpk spkBundles_any_of_hasFiredSpk hasFiredPrin hasFiredSess sessions_any_of_hasFiredSess liftFgBase fgPreInitPrin fgPreGenSPK fgPreInitiate pqxdhKeyIndFgPreImpl pqxdhKeyIndFgPreImpl_none_none_eq mem_support_liftFgBase mem_support_recordKeyIndResp pqxdhKeyIndFgPreImpl_preserves_hasFired evalDist_preSample_V_pqxdhKeyIndFgPreImpl evalDist_preSample_U_dh1_pqxdhKeyIndFgPreImpl fgPreInitiateAfterCoins fgPreInitiate_run_eq_afterCoins fgPreInitiate_before_c0 evalDist_preSample_U_dh3_pqxdhKeyIndFgPreImpl evalDist_runKeyIndFgSim_eq_preSample_dh3 evalDist_runKeyIndFgSim_eq_preSample_dh1 prob_badKeyIndFgDh3At_le_gapDh prob_badKeyIndFgDh1At_le_gapDh initDh1Cand respDh1Cand eraseSpkBundleEntryFg eraseSpkBundlesFg initDh1Cand_eq_of_ne_target respDh1Cand_eq_of_ne_target)
end SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security
export _root_.Proofs.SignalPqxdh.Security.FgGapDh (GdhBounded FgPoS FgPatchEntry FgKeyIndSimState fgEntryMatches fgPatch fgRoQueryGdh fgRunInitiateGdh fgRunAcceptOPKGdh fgRunAcceptNoOPKGdh fgKeyIndStep fgKeyIndGapDhRunAt fgKeyIndGapDhAdv gapDhDdhImpl gapDhFullImpl fgEntryMatchesPure fgPatchPure pureExtractCdhFromAdvRoLog pureExtractCdhFromAdvRoLog_wins_of_mem fgKeyIndGapDhAdvAt gapDhExp_fgKeyIndGapDhAdvAt_eq choosePartnerDrKeyRandPure mkSecretPosPure mkPairPosPure computeTwoSideOrPairPosPure computeOptPosPure fgRoQueryPure fgRunInitiatePure fgRunAcceptOPKPure fgRunAcceptNoOPKPure fgKeyIndStepPure simulateQ_gapDhFullImpl_fgRoQueryGdh simulateQ_gapDhFullImpl_fgRunInitiateGdh simulateQ_gapDhFullImpl_fgRunAcceptOPKGdh simulateQ_gapDhFullImpl_fgRunAcceptNoOPKGdh simulateQ_gapDhFullImpl_fgKeyIndStep RelProbUpToBad simulateQ_relProbUpToBad evalDist_simulateQ_eq_uniformBool_of_bad_preserved evalDist_simulateQ_eq_of_step_or_bad KeyIndFgCutoffState pqxdhKeyIndFgImpl runKeyIndFgSim badKeyIndFgDh1At badKeyIndFgDh3At badKeyIndFgAny prob_or_le_add_fg prob_badKeyIndFgAny_le_sum x25519_eq_iff_pow8_eq ddhEqPure_pair_pair_same_right_iff ddhEqPure_pair_pair_same_left_iff evalDist_simulateQ_preSample_slot_eq_of_hasFired evalDist_simulateQ_preSample_slot_eq evalDist_simulateQ_preSample_slot_eq_c0 initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt spkBundleFlatIdx_inj hasFiredSpk spkBundles_any_of_hasFiredSpk hasFiredPrin hasFiredSess sessions_any_of_hasFiredSess liftFgBase fgPreInitPrin fgPreGenSPK fgPreInitiate pqxdhKeyIndFgPreImpl pqxdhKeyIndFgPreImpl_none_none_eq mem_support_liftFgBase mem_support_recordKeyIndResp pqxdhKeyIndFgPreImpl_preserves_hasFired evalDist_preSample_V_pqxdhKeyIndFgPreImpl evalDist_preSample_U_dh1_pqxdhKeyIndFgPreImpl fgPreInitiateAfterCoins fgPreInitiate_run_eq_afterCoins fgPreInitiate_before_c0 evalDist_preSample_U_dh3_pqxdhKeyIndFgPreImpl evalDist_runKeyIndFgSim_eq_preSample_dh3 evalDist_runKeyIndFgSim_eq_preSample_dh1 prob_badKeyIndFgDh3At_le_gapDh prob_badKeyIndFgDh1At_le_gapDh respBundleKey initDh1Cand respDh1Cand eraseSpkBundleEntryFg eraseSpkBundlesFg initDh1Cand_eq_of_ne_target respDh1Cand_eq_of_ne_target)
end Proofs.SignalPqxdh.Security
