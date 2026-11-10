/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhIkInv
import VCVio.EvalDist.Monad.Basic

/-!
# Case B (`DH2`) Step Coupling and `GapDH` Bound

Per-query couplings between the pre-sampled game `pqxdhKeyIndFgPreImplIk` and the `GapDH`
simulator `fgKeyIndSimImplIk` under `FgSimInvDh2`, yielding `prob_badKeyIndFgDh2At_le_gapDh`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Ik

open Proofs.SignalPqxdh.Security.FgGapDh

theorem deadDh2_sess_map_eq {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S} (f : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S)
    (hfSid : ∀ s, (f s).sid = s.sid) (hfPeer : ∀ s, (f s).peerIkPk = s.peerIkPk)
    (hPrin : hst2.base.principals = hst1.base.principals)
    (hSessEq : hst2.base.sessions = hst1.base.sessions.map f) :
    deadDh2 P sIdx kIdx V hst2 = deadDh2 P sIdx kIdx V hst1 := by
  rw [deadDh2_eq_of_prin_sess P sIdx kIdx V hPrin]
  rw [hSessEq, List.find?_map]
  have hPred : (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) ∘ f =
      (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) := by
    funext s; simp [hfSid]
  rw [hPred, Option.map_map]
  congr 1
  funext s
  simp [hfPeer]

theorem deadDh2_prin_cons_eq {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S} (u : ℕ) (e : PrincipalEntry)
    (hPrin : hst2.base.principals = (u, e) :: hst1.base.principals)
    (hSess : hst2.base.sessions = hst1.base.sessions)
    (hAny : hst1.base.principals.any (fun (idx, _) => idx == u) = false)
    (hTgt : (u == kIdx) = true → e.ikAPk = V ∧ e.corrupted = false) :
    deadDh2 P sIdx kIdx V hst2 = deadDh2 P sIdx kIdx V hst1 := by
  have hSD : sessDeadIk P sIdx V hst2 = sessDeadIk P sIdx V hst1 :=
    sessDeadIk_eq_of_sess P sIdx V (by rw [hSess])
  unfold deadDh2
  rw [hSD]
  unfold prinTargetIsV deadDh1
  rw [hPrin]
  by_cases hU : (u == kIdx) = true
  · obtain ⟨hV, hC⟩ := hTgt hU
    have hNone : hst1.base.principals.find? (fun (idx, _) => idx == kIdx) = none := by
      rw [← beq_iff_eq.mp hU, List.find?_eq_none]
      intro x hx
      have := List.any_eq_false.mp hAny x hx
      simpa using this
    simp [hU, hV, hC, hNone]
  · have hUF : (u == kIdx) = false := Bool.eq_false_iff.mpr hU
    simp [hUF]

theorem deadDh2_map_corrupted_of_ne {S : Setup} (P : Primitives) (sIdx kIdx u : ℕ) (V : Bytes)
    (hNe : (u == kIdx) = false) (hst : KeyIndFgCutoffState S) :
    deadDh2 P sIdx kIdx V { hst with base := { hst.base with
      principals := hst.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } } =
      deadDh2 P sIdx kIdx V hst := by
  unfold deadDh2
  rw [prinTargetIsV_map_corrupted kIdx u V (hst1 := hst) rfl,
    deadDh1_map_corrupted_of_ne kIdx u hNe hst]
  rfl

theorem deadDh2_map_corrupted_eq_true_of_eq {S : Setup} (P : Primitives) (sIdx kIdx u : ℕ)
    (V : Bytes) (hEq : (u == kIdx) = true) (hst : KeyIndFgCutoffState S)
    (hT : prinTargetIsV kIdx V hst = true) (u0 : ℕ) (uEntry : PrincipalEntry)
    (hF : hst.base.principals.find? (fun (idx, _) => idx == u) = some (u0, uEntry)) :
    deadDh2 P sIdx kIdx V { hst with base := { hst.base with
      principals := hst.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } } = true := by
  unfold deadDh2
  rw [prinTargetIsV_map_corrupted kIdx u V (hst1 := hst) rfl, hT,
    deadDh1_map_corrupted_eq_true_of_eq kIdx u hEq hst u0 uEntry hF]
  rfl

/-! ## Simple and accept queries -/

theorem fgStepCoupling_dh2_unchanged (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (r : KeyIndResponse)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[k1 (r, hst)] {true} ≤ 𝒟[k2 (r, st)] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact hCont r hst st hDead ⟨h1, h2, h3, by omega, by omega, h6, h7, h8, h9, h10, h11⟩

theorem fgStepCoupling_dh2_initPrin (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true kIdx (noSpkIdx S) (some vSk) none S P (.initPrin u)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true kIdx (noSpkIdx S) S b.q_total
          (P.x25519Base vSk) (P.x25519Base vSk) (.initPrin u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinAnyEq : st.base.principals.any (fun (idx, _) => idx == u.val) =
      hst.base.principals.any (fun (idx, _) => idx == u.val) := by
    rw [hBaseEq]; exact any_idx_erasePrincipalsFg kIdx u.val hst.base.principals
  unfold pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and,
    hPrinAnyEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hTgt : (u.val == kIdx) = true
    · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        evalDist_sampleScalar32_const]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
      let entry1 : PrincipalEntry := {
        secIKA0 := vSk, ikAPk := P.x25519Base vSk,
        secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
      have hTgtV' : prinTargetIsV kIdx (P.x25519Base vSk)
          { hst with base := { hst.base with principals :=
            (u.val, entry1) :: hst.base.principals } } = true := by
        unfold prinTargetIsV at hTgtV ⊢
        simp [List.all_cons, entry1, hTgtV]
      apply hCont (.initPrinResp entry1.ikAPk entry1.ikSignPk)
      · refine Eq.trans ?_ hDead
        exact deadDh2_prin_cons_eq P sIdx kIdx _ (hst1 := hst) u.val entry1 rfl rfl hAny
          (fun _ => ⟨rfl, rfl⟩)
      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hTgtV', ?_, hSpks,
          hOpks, hSess⟩
        · rw [hBaseEq]
          simp [eraseStateFgIk, erasePrincipalsFg, erasePrincipalEntryFg, beq_iff_eq.mp hTgt]
        · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hvSk, rfl, fun _ => rfl⟩
          · exact hPrins kv hMem
    · have hTgtF : (u.val == kIdx) = false := Bool.eq_false_iff.mpr hTgt
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKA0 hSec0 => ?_)
      have hLen0 : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
      let entry1 : PrincipalEntry := {
        secIKA0 := secIKA0, ikAPk := P.x25519Base secIKA0,
        secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
      have hTgtV' : prinTargetIsV kIdx (P.x25519Base vSk)
          { hst with base := { hst.base with principals :=
            (u.val, entry1) :: hst.base.principals } } = true := by
        unfold prinTargetIsV at hTgtV ⊢
        simp [List.all_cons, hTgtF, hTgtV]
      apply hCont (.initPrinResp entry1.ikAPk entry1.ikSignPk)
      · refine Eq.trans ?_ hDead
        exact deadDh2_prin_cons_eq P sIdx kIdx _ (hst1 := hst) u.val entry1 rfl rfl hAny
          (fun h => by rw [hTgtF] at h; cases h)
      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hTgtV', ?_, hSpks,
          hOpks, hSess⟩
        · rw [hBaseEq]
          simp [eraseStateFgIk, erasePrincipalsFg, erasePrincipalEntryFg,
            beq_eq_false_iff_ne.mp hTgtF]
        · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hLen0, rfl, fun h => by rw [hTgtF] at h; cases h⟩
          · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh2_corruptIK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.corruptIK u)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg kIdx idx e)) := by
    rw [hBaseEq]; exact find?_idx_erasePrincipalsFg kIdx u.val hst.base.principals
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinFind, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    dsimp only [Option.map]
    simp only [StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont
  | some p =>
    rcases p with ⟨u0, entry⟩
    dsimp only [Option.map]
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    have hu0 : u0 = u.val := beq_iff_eq.mp (List.find?_some (p :=
      fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
    by_cases hTgt : (u.val == kIdx) = true
    · rw [hDeadCont _ _ (deadDh2_map_corrupted_eq_true_of_eq P sIdx kIdx u.val _ hTgt hst hTgtV u0
        entry hF)]
      exact zero_le
    · have hTgtF : (u.val == kIdx) = false := Bool.eq_false_iff.mpr hTgt
      have hu0F : (u0 == kIdx) = false := by rw [hu0]; exact hTgtF
      have hEraseEq : erasePrincipalEntryFg kIdx u0 entry = entry := by
        unfold erasePrincipalEntryFg; simp [hu0F]
      rw [hEraseEq]
      apply hCont (.corrResp entry.secIKA0 entry.secIKAsign)
      · rw [deadDh2_map_corrupted_of_ne P sIdx kIdx u.val _ hTgtF hst]
        exact hDead
      · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, ?_, ?_, hSpks, hOpks,
          hSess⟩
        · rw [hBaseEq]
          dsimp [eraseStateFgIk]
          rw [corrupt_map_erasePrincipalsFg]
        · exact ⟨(validPrincipals_map_corrupted S P u.val hst.base.principals hValidEc.1).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
        · rw [prinTargetIsV_map_corrupted kIdx u.val _ (hst1 := hst) rfl]; exact hTgtV
        · intro kv hkv
          rw [List.mem_map] at hkv
          rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
          have hPr := hPrins (idx, e) heMem
          by_cases hIdx : idx == u.val <;> simp only [hIdx, ↓reduceIte,
            Bool.false_eq_true] at hEq <;>
            (subst hEq; exact hPr)

theorem fgStepCoupling_dh2_genOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.genOPK u j o)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genOPK u j o) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
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
    · rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hTgtV,
        hPrins, hSpks, ?_, hSess⟩
      · exact ⟨hValidEc.1, hValidEc.2.1,
          (validOpkEntries_cons S u j o oEntry hst.base.opkEntries hValidEc.2.2.1 hAny).1,
          hValidEc.2.2.2⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen, rfl⟩
        · exact hOpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh2_genSPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.genSPK u j)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg kIdx idx e)) := by
    rw [hBaseEq]; exact find?_idx_erasePrincipalsFg kIdx u.val hst.base.principals
  have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
  have hTgtF : (spkBundleFlatIdx S u j == noSpkIdx S) = false :=
    spkBundleFlatIdx_ne_noSpkIdx S u j
  unfold pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkEq, hPrinFind, bind_assoc,
    pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some p =>
      rcases p with ⟨u0, uEntry⟩
      dsimp only [Option.map]
      simp only [erasePrincipalEntryFg_secIKAsign, erasePrincipalEntryFg_ikAPk]
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
      · rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]
        exact hDead
      · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega, ?_, hTgtV,
          hPrins, ?_, hOpks, hSess⟩
        · exact ⟨hValidEc.1,
            (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
            hValidEc.2.2.1, hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hSpkLen, rfl⟩
          · exact hSpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh2_roQuery (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (secrets : Bytes) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.roQuery secrets)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roQuery secrets) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  refine fgRoQuery_coupling (FgSlotReps.ofDh2 P hP uSk vSk huSk hvSk) hCache hFgLen
    (fun dk roCache' rawRoCache' fgL' hCache' hFgLen' => ?_)
  apply hCont (.drKeyResp dk)
  · rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead
  · exact ⟨hBaseEq, ⟨by dsimp; rw [hAdvEq.1], hAdvEq.2⟩, hCache', hFgLen',
      by dsimp [List.length_cons]; omega, hValidEc, hTgtV, hPrins, hSpks, hOpks, hSess⟩

theorem fgStepCoupling_dh2_revealDhSecrets (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P .revealDhSecrets).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) .revealDhSecrets st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, ↓reduceIte,
    StateT.run_pure, pure_bind]
  exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv
    .noneResp k1 k2 hCont

theorem fgStepCoupling_dh2_testSession (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.testSession sid)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.testSession sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  refine fgTestSession_coupling (eraseSessionEntryFg sIdx)
    (by rw [hBaseEq]; exact isFreshKeyIndSession_eraseStateFgIk sIdx kIdx hst.base sid)
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl)
    (by rw [hBaseEq]; exact find?_sid_eraseSessionsFg sIdx sid hst.base.sessions)
    (eraseSessionEntryFg_drKeyReal sIdx) (eraseSessionEntryFg_drKeyRand sIdx)
    (fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun r => hCont r _ _
      (Eq.trans (deadDh2_sess_map_eq P sIdx kIdx _ (hst1 := hst)
        (fun s => if s.sid == sid then { s with tested := true } else s)
        (fun s => by split_ifs <;> rfl) (fun s => by split_ifs <;> rfl) rfl rfl) hDead)
      ⟨by rw [hBaseEq]; dsimp [eraseStateFgIk]; rw [test_map_eraseSessionsFg],
        hAdvEq, hCache, by dsimp; omega, by dsimp; omega, validKeyIndEc_map_tested sid hValidEc,
        hTgtV, hPrins, hSpks, hOpks,
        fun s hs => by
          rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
          cases s0.sid == sid <;> exact hSess s0 hs0⟩)
    (fun r => hCont r _ _
      (by rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
        validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hTgtV, hPrins, hSpks, hOpks, hSess⟩)

theorem fgStepCoupling_dh2_revealSessionKey (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.revealSessionKey
      sid)).run hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.revealSessionKey sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  refine fgRevealSessionKey_coupling (eraseSessionEntryFg sIdx)
    (by rw [hBaseEq]; rfl)
    (by rw [hBaseEq]; exact find?_sid_eraseSessionsFg sIdx sid hst.base.sessions)
    (eraseSessionEntryFg_tested sIdx) (eraseSessionEntryFg_drKeyReal sIdx)
    (fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun r => hCont r _ _
      (Eq.trans (deadDh2_sess_map_eq P sIdx kIdx _ (hst1 := hst)
        (fun s => if s.sid == sid then { s with revealed := true } else s)
        (fun s => by split_ifs <;> rfl) (fun s => by split_ifs <;> rfl) rfl rfl) hDead)
      ⟨by rw [hBaseEq]; dsimp [eraseStateFgIk]; rw [reveal_map_eraseSessionsFg],
        hAdvEq, hCache, by dsimp; omega, by dsimp; omega, validKeyIndEc_map_revealed sid hValidEc,
        hTgtV, hPrins, hSpks, hOpks,
        fun s hs => by
          rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
          cases s0.sid == sid <;> exact hSess s0 hs0⟩)
    (fun r => hCont r _ _
      (by rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
        validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hTgtV, hPrins, hSpks, hOpks, hSess⟩)

theorem fgStepCoupling_dh2_registerKey (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sk : Bytes) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.registerKey sk)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.registerKey sk) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  exact fgRegisterKey_coupling
    (fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun hSkLen32 => hCont _ _ _
      (by rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, fgAdvEq_registerKey hSkLen32 hAdvEq, hCache,
        by dsimp; omega, by dsimp; omega, validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl,
        hTgtV, hPrins, hSpks, hOpks, hSess⟩)

theorem fgStepCoupling_dh2_acceptNoOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.acceptNoOPK k j l
      hdr)).run hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.acceptNoOPK k j l hdr) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh2 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hTakePrin : st.base.principals.take S.N_dh = erasePrincipalsFg kIdx hst.base.principals := by
    rw [hBaseEq]; exact List.take_of_length_le (by dsimp [eraseStateFgIk]; rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk := by
    rw [hBaseEq]
    exact koskSenderOkTake_erasePrincipalsFg_eq S P kIdx hst.base.principals st.advKeyPows
      hst.base.advKeys hdr.ikAPk hLengths.1 hAdvEq.2.1
  refine fgAcceptNoOPK_coupling R hP (erasePrincipalEntryFg kIdx) (fun _ b => b)
    hCache hFgLen hValidEc hAdvEq (fun kv hkv => ⟨(hPrins kv hkv).1, (hPrins kv hkv).2.1⟩)
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) hKoskEq
    (by rw [hBaseEq]; exact find?_idx_erasePrincipalsFg kIdx k.val hst.base.principals)
    (by rw [hBaseEq, option_map_prod_id]; rfl)
    (erasePrincipalEntryFg_ikAPk kIdx) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      rw [hTakePrin]
      exact findHonestPrincipal_erasePrincipalsFg_isSome P kIdx hst.base.principals hdr.ikAPk)
    (fun rInit => by
      rw [hBaseEq]; exact choosePartnerDrKeyRandPure_eraseSessionsFg P sIdx hst.base.sessions rInit)
    (fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun k0 kEntry kb0 bEntry hkMem hbMem _hIkOnCurve hEkOnCurve => ?_)
    (fun r rEntry roCache' fgL' hValidEc' hCache' hFgLen' =>
      hCont r _ _ (by rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead)
        ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache', hFgLen', by dsimp; omega,
          hValidEc', hTgtV, hPrins, hSpks, hOpks, hSess⟩)
  refine ⟨?_,
    computeTwoSideOrPairPosPure_erasePrin_fgPosRightRep P hP kIdx vSk k0 kEntry
      hdr.ekAPk (hPrins (k0, kEntry) hkMem) hEkOnCurve,
    ?_⟩
  · rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ikAPk
      bEntry.spkPk (hSpks (kb0, bEntry) hbMem).1]
    exact R.sec1 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
  · rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ekAPk
      bEntry.spkPk (hSpks (kb0, bEntry) hbMem).1]
    exact R.sec3 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)

theorem fgStepCoupling_dh2_acceptOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P (.acceptOPK k j o
      hdr)).run hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx (noSpkIdx S) S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.acceptOPK k j o hdr) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh2 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hTakePrin : st.base.principals.take S.N_dh = erasePrincipalsFg kIdx hst.base.principals := by
    rw [hBaseEq]; exact List.take_of_length_le (by dsimp [eraseStateFgIk]; rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk := by
    rw [hBaseEq]
    exact koskSenderOkTake_erasePrincipalsFg_eq S P kIdx hst.base.principals st.advKeyPows
      hst.base.advKeys hdr.ikAPk hLengths.1 hAdvEq.2.1
  refine fgAcceptOPK_coupling R hP (erasePrincipalEntryFg kIdx) (fun _ b => b)
    hCache hFgLen hValidEc hAdvEq (fun kv hkv => ⟨(hPrins kv hkv).1, (hPrins kv hkv).2.1⟩) hOpks
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) hKoskEq
    (by rw [hBaseEq]; exact find?_idx_erasePrincipalsFg kIdx k.val hst.base.principals)
    (by rw [hBaseEq, option_map_prod_id]; rfl)
    (erasePrincipalEntryFg_ikAPk kIdx) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      rw [hTakePrin]
      exact findHonestPrincipal_erasePrincipalsFg_isSome P kIdx hst.base.principals hdr.ikAPk)
    (fun rInit => by
      rw [hBaseEq]; exact choosePartnerDrKeyRandPure_eraseSessionsFg P sIdx hst.base.sessions rInit)
    (fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun k0 kEntry kb0 bEntry hkMem hbMem _hIkOnCurve hEkOnCurve => ?_)
    (fun r rEntry roCache' fgL' hValidEc' hOpks' hCache' hFgLen' =>
      hCont r _ _ (by rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead)
        ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache', hFgLen', by dsimp; omega,
          hValidEc', hTgtV, hPrins, hSpks, hOpks', hSess⟩)
  refine ⟨?_,
    computeTwoSideOrPairPosPure_erasePrin_fgPosRightRep P hP kIdx vSk k0 kEntry
      hdr.ekAPk (hPrins (k0, kEntry) hkMem) hEkOnCurve,
    ?_⟩
  · rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ikAPk
      bEntry.spkPk (hSpks (kb0, bEntry) hbMem).1]
    exact R.sec1 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
  · rw [computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk hdr.ekAPk
      bEntry.spkPk (hSpks (kb0, bEntry) hbMem).1]
    exact R.sec3 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)


/-! ## Initiate coupling -/

theorem lookupSpkSkTake_len32_pow8
    (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows advKeys : List (Bytes × Bytes)) (pk : Bytes)
    (hSpks : ∀ kv ∈ spkBundles, kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk)
    (hS : spkBundles.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk') => (sk, P.pow8 pk')))
    (hAdvSkLen : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hSpkReg : (isGameSpk P spkBundles pk || isAdvRegistered P advKeys pk) = true) :
    (lookupSpkSkTake S P spkBundles advKeyPows pk).length = 32 ∧
      P.pow8 pk = P.pow8 (P.x25519Base (lookupSpkSkTake S P spkBundles advKeyPows pk)) := by
  unfold lookupSpkSkTake
  dsimp only
  rw [List.take_of_length_le hS]
  cases hFB : spkBundles.find? (fun (_, b) => P.pow8 b.spkPk == P.pow8 pk) with
  | some kb =>
    rcases kb with ⟨k, bEntry⟩
    dsimp only
    have hbMem := List.mem_of_find?_eq_some hFB
    have hbPow : P.pow8 bEntry.spkPk = P.pow8 pk :=
      beq_iff_eq.mp (List.find?_some (p :=
        fun (x : (Nat × Nat) × SpkBundleEntry) => P.pow8 x.2.spkPk == P.pow8 pk) hFB)
    rcases hSpks (k, bEntry) hbMem with ⟨hbLen, hbPk⟩
    exact ⟨hbLen, by rw [← hbPow, hbPk]⟩
  | none =>
    dsimp only
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
      exact ⟨hLen0, by rw [← hPowEq, ← hpow0Eq, hPk0]⟩

theorem computeTwoSideOrPairPosPure_erasePrin_lookupSpkSkTake_secret
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (kIdx : ℕ)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (u : Nat) (uEntry : PrincipalEntry) (pk : Bytes)
    (huLen : uEntry.secIKA0.length = 32) (huPk : uEntry.ikAPk = P.x25519Base uEntry.secIKA0)
    (hSpks : ∀ kv ∈ spkBundles, kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk)
    (hS : spkBundles.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk') => (sk, P.pow8 pk')))
    (hAdvSkLen : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hSpkReg : (isGameSpk P spkBundles pk || isAdvRegistered P advKeys pk) = true) :
    computeTwoSideOrPairPosPure P (erasePrincipalEntryFg kIdx u uEntry).secIKA0
        (lookupSpkSkTake S P spkBundles advKeyPows pk) uEntry.ikAPk pk =
      mkSecretPosPure P (P.x25519 uEntry.secIKA0 pk) := by
  dsimp only [erasePrincipalEntryFg]
  by_cases hIdx : (u == kIdx) = true
  · simp only [hIdx, ↓reduceIte]
    rcases lookupSpkSkTake_len32_pow8 S P spkBundles advKeyPows advKeys pk
      hSpks hS hAdvPows hAdvSkLen hSpkReg with ⟨hLen, hPow⟩
    rw [computeTwoSideOrPairPosPure_nil_right_len32 P _ uEntry.ikAPk pk hLen, huPk,
      ← hP.toWellFormedPrimitivesδ.x25519_comm uEntry.secIKA0,
      ← hP.toWellFormedPrimitivesδ.x25519_pow8_congr uEntry.secIKA0 pk _
          (hP.pow8_base_len pk _ hPow) (hP.x25519Base_len _) hPow]
  · have hIdxF : (u == kIdx) = false := Bool.eq_false_iff.mpr hIdx
    simp only [hIdxF, Bool.false_eq_true, ↓reduceIte]
    exact computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 _ uEntry.ikAPk pk huLen

theorem koskBundleOkTake_erasePrin_eq (S : Setup) (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) :
    koskBundleOkTake S P (erasePrincipalsFg kIdx principals) spkBundles opkEntries advKeyPows
      bundle =
    koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  rw [koskBundleOkTake_eq_of_le S P (erasePrincipalsFg kIdx principals) spkBundles opkEntries
    advKeyPows advKeys bundle (by rw [erasePrincipalsFg_length]; exact hP) hS hO hAdvPows]
  unfold koskBundleOk
  rw [isGameIdKey_erasePrincipalsFg]

theorem checkBundleProvenanceTake_erasePrin_eq (S : Setup) (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh) :
    checkBundleProvenanceTake S P (erasePrincipalsFg kIdx principals) spkBundles opkEntries bundle =
      checkBundleProvenance P principals spkBundles opkEntries bundle := by
  rw [checkBundleProvenanceTake_eq_of_le S P _ _ _ _
    (by rw [erasePrincipalsFg_length]; exact hP) hS hO]
  rw [checkBundleProvenance_erasePrincipalsFg]

theorem deadDh2_sess_cons_tgt_alive {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S} (e : KeyIndInitiatorEntry S)
    (hPrin : hst2.base.principals = hst1.base.principals)
    (hSessEq : hst2.base.sessions = e :: hst1.base.sessions)
    (hSlot : (initSessionSlotIdx e.sid == sIdx) = true)
    (hPow : P.pow8 e.peerIkPk = P.pow8 V)
    (hD : deadDh2 P sIdx kIdx V hst1 = false) :
    deadDh2 P sIdx kIdx V hst2 = false := by
  unfold deadDh2 at hD ⊢
  have hT' : prinTargetIsV kIdx V hst2 = prinTargetIsV kIdx V hst1 := by
    unfold prinTargetIsV; rw [hPrin]
  have hS : sessDeadIk P sIdx V hst2 = false := by
    unfold sessDeadIk
    rw [hSessEq, List.find?_cons, hSlot]
    simp [hPow]
  rw [hT', deadDh1_eq_of_principals kIdx hPrin, hS]
  revert hD
  cases prinTargetIsV kIdx V hst1 <;> cases deadDh1 kIdx hst1 <;> simp

theorem deadDh2_sess_cons_tgt_dead {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S} (e : KeyIndInitiatorEntry S)
    (hPrin : hst2.base.principals = hst1.base.principals)
    (hSessEq : hst2.base.sessions = e :: hst1.base.sessions)
    (hSlot : (initSessionSlotIdx e.sid == sIdx) = true)
    (hPow : P.pow8 e.peerIkPk ≠ P.pow8 V)
    (hT : prinTargetIsV kIdx V hst1 = true) :
    deadDh2 P sIdx kIdx V hst2 = true := by
  unfold deadDh2
  have hT' : prinTargetIsV kIdx V hst2 = prinTargetIsV kIdx V hst1 := by
    unfold prinTargetIsV; rw [hPrin]
  have hS : sessDeadIk P sIdx V hst2 = true := by
    unfold sessDeadIk
    rw [hSessEq, List.find?_cons, hSlot]
    simp [hPow]
  rw [hT', hT, hS]
  simp

theorem deadDh2_sess_cons_nontgt {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S} (e : KeyIndInitiatorEntry S)
    (hPrin : hst2.base.principals = hst1.base.principals)
    (hSessEq : hst2.base.sessions = e :: hst1.base.sessions)
    (hSlot : (initSessionSlotIdx e.sid == sIdx) = false) :
    deadDh2 P sIdx kIdx V hst2 = deadDh2 P sIdx kIdx V hst1 := by
  refine deadDh2_eq_of_prin_sess P sIdx kIdx V hPrin ?_
  rw [hSessEq, List.find?_cons, hSlot]

theorem fgStepCoupling_dh2_initiate (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(do
        let x ← (fgPreInitiate false sIdx (some uSk) S P sid u bundle).run hst.base
        k1 (x.1, { base := x.2, advRoLog := hst.advRoLog }))] {true} ≤
      𝒟[fgRunInitiatePure P P.isValidDhTriple false sIdx S b.q_total
          (P.x25519Base uSk) sid u bundle st >>= k2] {true} := by
  let R := FgSlotReps.ofDh2 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
    hOpks, hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hRespLen : hst.base.respSessions.length ≤ S.N_sess_tot :=
    validKeyIndEc_resp_length_le_fg S hst.base hValidEc
  have hRespEq : st.base.respSessions = hst.base.respSessions := by rw [hBaseEq]; rfl
  have hAnyEq : st.base.sessions.any (fun e => e.sid == sid) =
      hst.base.sessions.any (fun e => e.sid == sid) := by
    rw [hBaseEq]; exact any_sid_eraseSessionsFg sIdx sid hst.base.sessions
  have hPrinEq : st.base.principals = erasePrincipalsFg kIdx hst.base.principals :=
    by rw [hBaseEq]; rfl
  have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := by rw [hBaseEq]; rfl
  have hPrinFind : (erasePrincipalsFg kIdx hst.base.principals).find? (fun (idx,
      _) => idx == u.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg kIdx idx e)) :=
    find?_idx_erasePrincipalsFg kIdx u.val hst.base.principals
  have hTakePrin : (erasePrincipalsFg kIdx hst.base.principals).take S.N_dh =
      erasePrincipalsFg kIdx hst.base.principals :=
    List.take_of_length_le (by rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskBundleOkTake S P (erasePrincipalsFg kIdx hst.base.principals)
        hst.base.spkBundles hst.base.opkEntries st.advKeyPows bundle =
      koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries hst.base.advKeys
        bundle :=
    koskBundleOkTake_erasePrin_eq S P kIdx hst.base.principals hst.base.spkBundles
      hst.base.opkEntries
      st.advKeyPows hst.base.advKeys bundle hLengths.1 hLengths.2.1 hLengths.2.2.1 hAdvEq.2.1
  have hProvEq : checkBundleProvenanceTake S P (erasePrincipalsFg kIdx hst.base.principals)
        hst.base.spkBundles hst.base.opkEntries bundle =
      checkBundleProvenance P hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle :=
    checkBundleProvenanceTake_erasePrin_eq S P kIdx hst.base.principals hst.base.spkBundles
      hst.base.opkEntries bundle hLengths.1 hLengths.2.1 hLengths.2.2.1
  unfold fgPreInitiate fgRunInitiatePure
  simp only [StateT.run_bind, StateT.run_get, hAnyEq, hPrinEq, hSpkEq, hOpkEq, hRespEq, hPrinFind,
    hTakePrin,
    hKoskEq, resolveSigPk_erasePrincipalsFg, isHonestUncorruptedPeer_erasePrincipalsFg,
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
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some pu =>
      rcases pu with ⟨u0, uEntry⟩
      simp only [Option.map_some]
      have huMem := List.mem_of_find?_eq_some hFU
      rcases hPrins (u0, uEntry) huMem with ⟨huSkLen, huPk, _⟩
      by_cases hKosk : (!koskBundleOk P hst.base.principals hst.base.spkBundles
        hst.base.opkEntries hst.base.advKeys bundle) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      · have hKoskT : koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
          hst.base.advKeys bundle = true :=
          of_not_not_eq_true hKosk
        have hSpkReg : (isGameSpk P hst.base.spkBundles bundle.spkB || isAdvRegistered P
          hst.base.advKeys bundle.spkB) = true := by
          unfold koskBundleOk at hKoskT
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hKoskT).1).2
        have hPos1Eq := computeTwoSideOrPairPosPure_erasePrin_lookupSpkSkTake_secret S P hP kIdx
          hst.base.spkBundles st.advKeyPows hst.base.advKeys u0 uEntry bundle.spkB huSkLen huPk
          hSpks hLengths.2.1 hAdvEq.2.1 hAdvEq.2.2 hSpkReg
        have hPos1 : FgPosLeftRep P uSk (mkSecretPosPure P (P.x25519 uEntry.secIKA0 bundle.spkB))
            (P.x25519 uEntry.secIKA0 bundle.spkB) :=
          R.sec1 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
        simp only [hKosk, Bool.false_eq_true, ↓reduceIte, erasePrincipalEntryFg_ikAPk, hPos1Eq]
        by_cases hTgt : (initSessionSlotIdx sid == sIdx) = true
        · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind, evalDist_sampleScalar32_const]
          refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
          by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
               bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM
                 bundle.pqspkB) bundle.pqspkSig)) = true
          · simp only [hSig, ↓reduceIte, StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
          · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
            cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              dsimp only
              by_cases hPowV : (P.pow8 bundle.ikB == P.pow8 (P.x25519Base vSk)) = true
              · have hPowEq : P.pow8 bundle.ikB = P.pow8 (P.x25519Base vSk) := beq_iff_eq.mp hPowV
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 uSk bundle.ikB
                let dh3 := P.x25519 uSk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 uSk opkPk)
                let pos1 := mkSecretPosPure P (P.x25519 uEntry.secIKA0 bundle.spkB)
                let pos2 := computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.ikB
                let pos3 := computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.spkB
                let pos4? := computeOptPosPure P [] (P.x25519Base uSk) (bundle.opkB?.map (fun (_,
                  opkPk) => ([], opkPk)))
                have hBundleOnCurve :=
                  onCurveKeyLocal_of_koskBundleOk P hst.base.principals hst.base.spkBundles
                    hst.base.opkEntries hst.base.advKeys bundle
                    (fun kv hkv => ⟨(hPrins kv hkv).1, (hPrins kv hkv).2.1⟩) hOpks hAdvEq.2.2 hKosk
                have hSpkOnCurve : onCurveKeyLocal P bundle.spkB := by
                  rcases (Bool.or_eq_true _ _).mp hSpkReg with hGame | hReg
                  · unfold isGameSpk at hGame
                    rcases List.any_eq_true.mp hGame with ⟨⟨idx0, b0⟩, hMem, hBeq⟩
                    rcases hSpks (idx0, b0) hMem with ⟨hLen, hPk0⟩
                    exact Or.inr ⟨b0.spkSk, hLen, by rw [← hPk0, (beq_iff_eq.mp hBeq).symm]⟩
                  · exact onCurveKeyLocal_of_isAdvRegistered P hst.base.advKeys bundle.spkB
                      hAdvEq.2.2 hReg
                have hPos2 : FgPosRightRep P vSk pos2 dh2 := by
                  dsimp only [pos2, dh2, computeTwoSideOrPairPosPure_nil_nil]
                  exact fgPosRightRep_mkPair_left_of_pow8 P hP.toWellFormedPrimitivesδ uSk vSk
                    bundle.ikB huSk hvSk (hP.pow8_base_len bundle.ikB vSk hPowEq) hPowEq
                have hPos3 : FgPosLeftRep P uSk pos3 dh3 := by
                  dsimp only [pos3, dh3, computeTwoSideOrPairPosPure_nil_nil]
                  exact fgPosLeftRep_mkPair_left P hP.toWellFormedPrimitivesδ uSk bundle.spkB
                    hSpkOnCurve
                have hPos4 : FgOptLeftRep P uSk pos4? dh4? :=
                  computeOptPosPure_nil_uSk_fgOptLeftRep P hP.toWellFormedPrimitivesδ uSk
                    bundle.opkB? hBundleOnCurve.2
                have hSsLen : ss.length = 32 :=
                  (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _ hEnc).1
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
                  · exact deadDh2_sess_cons_tgt_alive P sIdx kIdx _ (hst1 :=
                      hst) _ rfl rfl hTgt hPowEq hDead
                  · refine ⟨?_, hAdvEq, hCache', hFgLen', by dsimp; omega,
                      ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                        hTgtV, hPrins, hSpks, hOpks, ?_⟩
                    · rw [hBaseEq]; simp [eraseStateFgIk, eraseSessionsFg, eraseSessionEntryFg,
                        beq_iff_eq.mp hTgt, hProvEq]
                    · intro s hs
                      rcases List.mem_cons.mp hs with rfl | hMem
                      · exact ⟨huSk, rfl, fun _ => rfl⟩
                      · exact hSess s hMem
              ·
                have hPowNe : P.pow8 bundle.ikB ≠ P.pow8 (P.x25519Base vSk) :=
                  fun h => hPowV (beq_iff_eq.mpr h)
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind]
                refine le_trans (le_of_eq ?_) zero_le
                refine evalDist_bind_true_eq_zero_of_support _ _ (fun ⟨drKeyReal, roCache'⟩ _ => ?_)
                refine evalDist_bind_true_eq_zero_of_support _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                  simp only [StateT.run_pure, pure_bind] <;>
                  exact hDeadCont _ _ (deadDh2_sess_cons_tgt_dead P sIdx kIdx _ (hst1 :=
                    hst) _ rfl rfl hTgt hPowNe hTgtV)
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
            exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
          · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
            cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              dsimp only
              let ekAPk := P.x25519Base ekASk
              let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
              let dh2 := P.x25519 ekASk bundle.ikB
              let dh3 := P.x25519 ekASk bundle.spkB
              let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
              let pos1 := mkSecretPosPure P (P.x25519 uEntry.secIKA0 bundle.spkB)
              let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
              let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
              let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_,
                opkPk) => ([], opkPk)))
              have hPos2 : FgPosRightRep P vSk pos2 dh2 := by
                dsimp only [pos2, dh2]
                rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.ikB hEkLen]
                exact R.sec2 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos3 : FgPosLeftRep P uSk pos3 dh3 := by
                dsimp only [pos3, dh3]
                rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.spkB hEkLen]
                exact R.sec3 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos4 : FgOptLeftRep P uSk pos4? dh4? :=
                computeOptPosPure_left_len32_fgOptLeftRep P hP.toWellFormedPrimitivesδ uSk ekASk
                  ekAPk hEkLen bundle.opkB?
              have hSsLen : ss.length = 32 :=
                (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _ hEnc).1
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
                · refine Eq.trans ?_ hDead
                  exact deadDh2_sess_cons_nontgt P sIdx kIdx _ (hst1 := hst) _ rfl rfl hTgtF
                · refine ⟨?_, hAdvEq, hCache', hFgLen', by dsimp; omega,
                    ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                      hTgtV, hPrins, hSpks, hOpks, ?_⟩
                  · rw [hBaseEq]; simp [eraseStateFgIk, eraseSessionsFg, eraseSessionEntryFg,
                      beq_eq_false_iff_ne.mp hTgtF, hProvEq]
                  · intro s hs
                    rcases List.mem_cons.mp hs with rfl | hMem
                    · exact ⟨hEkLen, rfl, fun h => by rw [hTgtF] at h; cases h⟩
                    · exact hSess s hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont


/-! ## Case B `GapDH` bound -/

theorem fgStepCoupling_dh2 (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh2 P sIdx kIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImplIk sIdx kIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true} ≤
      𝒟[(fgKeyIndSimImplIk P P.isValidDhTriple sIdx kIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  rw [fgKeyIndSimImplIk_run]
  cases q with
  | initPrin u =>
    exact fgStepCoupling_dh2_initPrin S b P hP sIdx kIdx uSk vSk huSk hvSk u rem hst st hDead hInv
      k1 k2 hCont
  | corruptIK u =>
    exact fgStepCoupling_dh2_corruptIK S b P hP sIdx kIdx uSk vSk huSk hvSk u rem hst st hDead
      hInv k1 k2 hCont hDeadCont
  | genSPK u j =>
    exact fgStepCoupling_dh2_genSPK S b P hP sIdx kIdx uSk vSk huSk hvSk u j rem hst st hDead hInv
      k1 k2 hCont
  | genOPK u j o =>
    exact fgStepCoupling_dh2_genOPK S b P hP sIdx kIdx uSk vSk huSk hvSk u j o rem hst st hDead
      hInv k1 k2 hCont
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImplIk pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPureIk
      fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh2_initiate S b P hP sIdx kIdx uSk vSk huSk hvSk (.sendOPK u i)
        trivial u bundle rem hst st hDead hInv k1 k2 hCont hDeadCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImplIk pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPureIk
      fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh2_initiate S b P hP sIdx kIdx uSk vSk huSk hvSk (.sendNoOPK u i)
        trivial u bundle rem hst st hDead hInv k1 k2 hCont hDeadCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | acceptOPK k j o hdr =>
    exact fgStepCoupling_dh2_acceptOPK S b P hP sIdx kIdx uSk vSk huSk hvSk k j o hdr rem hst st
      hDead hInv k1 k2 hCont
  | acceptNoOPK k j l hdr =>
    exact fgStepCoupling_dh2_acceptNoOPK S b P hP sIdx kIdx uSk vSk huSk hvSk k j l hdr rem hst st
      hDead hInv k1 k2 hCont
  | testSession sid =>
    exact fgStepCoupling_dh2_testSession S b P hP sIdx kIdx uSk vSk huSk hvSk sid rem hst st hDead
      hInv k1 k2 hCont
  | revealSessionKey sid =>
    exact fgStepCoupling_dh2_revealSessionKey S b P hP sIdx kIdx uSk vSk huSk hvSk sid rem hst st
      hDead hInv k1 k2 hCont
  | roQuery secrets =>
    exact fgStepCoupling_dh2_roQuery S b P hP sIdx kIdx uSk vSk huSk hvSk secrets rem hst st hDead
      hInv k1 k2 hCont
  | revealDhSecrets =>
    exact fgStepCoupling_dh2_revealDhSecrets S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead
      hInv k1 k2 hCont
  | registerKey sk =>
    exact fgStepCoupling_dh2_registerKey S b P hP sIdx kIdx uSk vSk huSk hvSk sk rem hst st hDead
      hInv k1 k2 hCont
  | revealSpkSk u j =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hTgtV, hPrins, hSpks,
      hOpks, hSess⟩
    have hSpkEq : st.base.spkBundles = hst.base.spkBundles := by rw [hBaseEq]; rfl
    unfold pqxdhKeyIndFgPreImplIk pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl
      liftFgBase fgKeyIndStepPureIk fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkEq, bind_assoc, pure_bind]
    cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh2_unchanged S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some kb =>
      rcases kb with ⟨k0, bEntry⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      apply hCont (.spkSkResp bEntry.spkSk)
      · rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ rfl rfl]; exact hDead
      · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
          ⟨hValidEc.1, (validSpkBundles_map_revealed S P (u.val,
            j.val) hst.base.spkBundles hValidEc.2.1).1, hValidEc.2.2⟩,
          hTgtV, hPrins, ?_, hOpks, hSess⟩
        intro kv hkv
        rcases List.mem_map.mp hkv with ⟨⟨idx, b0⟩, hMem0, hEq0⟩
        have h0 := hSpks (idx, b0) hMem0
        split_ifs at hEq0 <;> subst hEq0 <;> exact h0

/-- Bounds the Case B (`DH2 = CDH(ek_U*, ik_V*)`) bad-event probability at `(sIdx, kIdx)` by the
    `GapDH` advantage of `fgKeyIndGapDhAdvAtIk sIdx kIdx S b A`. -/
theorem prob_badKeyIndFgDh2At_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (kIdx : ℕ) (_hkIdx : kIdx ∈ Finset.range S.N_id) :
    (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
        pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAtIk sIdx kIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx
  unfold GapDH
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim_eq_preSample_dh2 sIdx kIdx P A.1
    (fun x => pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhExp_fgKeyIndGapDhAdvAtIk_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh2 P sIdx kIdx (P.x25519Base vSk))
    (FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huLen hvLen)
    (pqxdhKeyIndFgPreImplIk sIdx kIdx (some uSk) (some vSk) S P)
    (fgKeyIndSimImplIk P P.isValidDhTriple sIdx kIdx S b.q_total (P.x25519Base uSk) (P.x25519Base
      vSk))
    (fun q s1 hD x hx => pqxdhKeyIndFgPreImplIk_preserves_deadDh2 P sIdx kIdx hsLt uSk vSk q s1 hD
      x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh2 S b P hP sIdx kIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2 hCont
        hDeadCont)
    (fun x => pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdh2FromAdvRoLog P.isValidDhTriple b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.advRoLog) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD => by simp [badKeyIndFgDh2At_eq_false_of_deadDh2 P b.q_ro sIdx kIdx (P.x25519Base
      vSk) s1 hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh2_terminal_le S b P hP b.q_ro sIdx kIdx uSk vSk huLen hvLen a rem s1 s2 hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyIndSimState.empty S secb)
    (fgSimInvDh2_empty S b P hP sIdx kIdx uSk vSk huLen hvLen secb)

end Proofs.SignalPqxdh.Security.FgGapDh.Ik
