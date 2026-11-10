/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.SigHopB
import VCVio.EvalDist.Monad.Basic

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

namespace SigGameLens

variable {S : Setup} {St R : Type} (L : SigGameLens S St R)

/-! ### `ActiveBefore` Step Lemmas -/

theorem before_step_initPrin (P : Primitives) (k : Nat) (u : Fin S.N_id)
    (st : St) (budget : Nat)
    (fL : R × St → ℝ≥0∞)
    (fR : Bytes → (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (hBefore : L.ActiveBefore P k st budget)
    (h_ih_before : ∀ out st' b', L.ActiveBefore P k st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), [])))
    (h_ih_after : ∀ sk out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR sk ((out, s', b'), msgs')) :
    probExpect ((L.realInitPrin P u).run st) fL ≤
      probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget (L.stepInitPrin P u ⟨st, k, P.sigPkGen sk,
            none⟩) []) (fR sk)) := by
  rcases hBefore with ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
  by_cases hAny : (L.prins st).any (fun (idx, _) => idx == u.val) = true
  · refine before_step_of_eq_real P k ((L.realInitPrin P u).run st)
      (fun pk => L.stepInitPrin P u ⟨st, k, pk, none⟩)
      (L.ActiveBefore P k) budget fL fR ?_ ?_ h_ih_before
    · intro pk
      unfold stepInitPrin realInitPrin
      simp [hAny]
    · intro x hx
      rcases L.mem_support_realInitPrin P u st x hx with rfl | ⟨hF, _⟩
      · exact ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
      · rw [hAny] at hF; cases hF
  · have hAnyF : (L.prins st).any (fun (idx, _) => idx == u.val) = false :=
      Bool.eq_false_iff.mpr hAny
    by_cases hu : (u.val == k) = true
    · have hu_eq : u.val = k := beq_iff_eq.mp hu
      have hL :
          probExpect ((L.realInitPrin P u).run st) fL =
          probExpect sampleScalar32 (fun secIKA0 =>
            probExpect sampleScalar32 (fun sk =>
              let entry : PrincipalEntry := {
                secIKA0    := secIKA0
                ikAPk      := P.x25519Base secIKA0
                secIKAsign := sk
                ikSignPk   := P.sigPkGen sk
                corrupted  := false
              }
              fL (L.initPrinResp (P.x25519Base secIKA0) (P.sigPkGen sk),
                  L.putPrins st ((u.val, entry) :: L.prins st)))) := by
        unfold realInitPrin
        simp [hAnyF, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
          StateT.run_set, pure_bind, probExpect_bind, probExpect_map]
      have hR1 : ∀ sk,
          probExpect (runSigStepSim P sk budget (L.stepInitPrin P u ⟨st, k, P.sigPkGen sk,
              none⟩) []) (fR sk) =
          probExpect sampleScalar32 (fun secIKA0 =>
            let rEntry : PrincipalEntry := {
              secIKA0    := secIKA0
              ikAPk      := P.x25519Base secIKA0
              secIKAsign := []
              ikSignPk   := P.sigPkGen sk
              corrupted  := false
            }
            fR sk ((L.initPrinResp (P.x25519Base secIKA0) (P.sigPkGen sk),
              ⟨L.putPrins st ((u.val, rEntry) :: L.prins st), k, P.sigPkGen sk, none⟩, budget),
                  [])) := by
        intro sk
        unfold runSigStepSim stepInitPrin
        simp [hAnyF, hu, probExpect_map]
      have hR :
          probExpect sampleScalar32 (fun sk =>
            probExpect (runSigStepSim P sk budget (L.stepInitPrin P u ⟨st, k, P.sigPkGen sk,
                none⟩) []) (fR sk)) =
          probExpect sampleScalar32 (fun secIKA0 =>
            probExpect sampleScalar32 (fun sk =>
              let rEntry : PrincipalEntry := {
                secIKA0    := secIKA0
                ikAPk      := P.x25519Base secIKA0
                secIKAsign := []
                ikSignPk   := P.sigPkGen sk
                corrupted  := false
              }
              fR sk ((L.initPrinResp (P.x25519Base secIKA0) (P.sigPkGen sk),
                ⟨L.putPrins st ((u.val, rEntry) :: L.prins st), k, P.sigPkGen sk, none⟩, budget),
                    []))) := by
        simp only [hR1]
        exact probExpect_swap sampleScalar32 sampleScalar32 _
      rw [hL, hR]
      refine probExpect_mono_of_support sampleScalar32 _ _ (fun secIKA0 _ => ?_)
      refine probExpect_mono_of_support sampleScalar32 _ _ (fun sk _ => ?_)
      let entry : PrincipalEntry := {
        secIKA0    := secIKA0
        ikAPk      := P.x25519Base secIKA0
        secIKAsign := sk
        ikSignPk   := P.sigPkGen sk
        corrupted  := false
      }
      let st' := L.putPrins st ((u.val, entry) :: L.prins st)
      have hCons := validPrincipals_cons S u entry (L.prins st) hVP hAnyF
      have hErase : L.eraseSk k st' =
          L.putPrins st ((u.val, { entry with secIKAsign := [] }) :: L.prins st) := by
        unfold st' eraseSk
        rw [L.prins_putPrins, L.putPrins_putPrins, hu_eq,
            erasePrinSk_cons_eq k entry (L.prins st),
            erasePrinSk_eq_self_of_not_mem k (L.prins st) hNotK]
      apply h_ih_after sk (L.initPrinResp (P.x25519Base secIKA0) (P.sigPkGen sk))
        st' ⟨L.putPrins st ((u.val, { entry with
                                      secIKAsign := [] }) :: L.prins st), k, P.sigPkGen sk,
                                      none⟩ budget []
      refine ⟨by rw [hErase], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [st'] using hCons.1
      · refine ⟨entry, ?_, rfl, rfl, rfl⟩
        simp [st', hu_eq]
      · simpa [st'] using hVS
      · simp only [st', L.spks_putPrins, hb_eq]
        exact Nat.le_add_right S.N_spk_tot (L.spks st).length
      · intro m hm; cases hm
      · simpa [st'] using cleanPeers_cons_principal S P k u.val entry (L.prins st) (L.badPeers st)
          hClean
    · have huF : (u.val == k) = false := Bool.eq_false_iff.mpr hu
      refine before_step_of_eq_real P k ((L.realInitPrin P u).run st)
        (fun pk => L.stepInitPrin P u ⟨st, k, pk, none⟩)
        (L.ActiveBefore P k) budget fL fR ?_ ?_ h_ih_before
      · intro pk
        unfold stepInitPrin
        simp [hAnyF, huF]
      · intro x hx
        rcases L.mem_support_realInitPrin P u st x hx with rfl | ⟨_, _, entry, rfl⟩
        · exact ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
        · have hCons := validPrincipals_cons S u entry (L.prins st) hVP hAnyF
          refine ⟨hb_eq, by simpa using hCons.1, ?_, by simpa using hVS, by simpa using hSpkNotK,
              ?_⟩
          · intro p hp
            simp only [L.prins_putPrins, List.mem_cons] at hp
            rcases hp with rfl | hmem
            · exact beq_eq_false_iff_ne.mp huF
            · exact hNotK p hmem
          · simpa using cleanPeers_cons_principal S P k u.val entry (L.prins st) (L.badPeers st)
              hClean

theorem before_step_corruptIK (P : Primitives) (k : Nat) (u : Fin S.N_id)
    (st : St) (budget : Nat)
    (fL : R × St → ℝ≥0∞)
    (fR : Bytes → (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (hBefore : L.ActiveBefore P k st budget)
    (h_ih_before : ∀ out st' b', L.ActiveBefore P k st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) :
    probExpect ((L.realCorruptIK u).run st) fL ≤
      probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget (L.stepCorruptIK u ⟨st, k, P.sigPkGen sk,
            none⟩) []) (fR sk)) := by
  rcases hBefore with ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
  refine before_step_of_eq_real P k ((L.realCorruptIK u).run st)
    (fun pk => L.stepCorruptIK u ⟨st, k, pk, none⟩)
    (L.ActiveBefore P k) budget fL fR ?_ ?_ h_ih_before
  · intro pk
    unfold stepCorruptIK
    by_cases hu : (u.val == k) = true
    · have hu_eq : u.val = k := beq_iff_eq.mp hu
      have hNone : (L.prins st).find? (fun (idx, _) => idx == u.val) = none := by
        rw [List.find?_eq_none]
        intro ⟨idx, e⟩ hmem hbeq
        exact hNotK (idx, e) hmem ((beq_iff_eq.mp hbeq).trans hu_eq)
      unfold realCorruptIK
      simp [hu, hNone]
    · simp [hu]
  · intro x hx
    rcases L.mem_support_realCorruptIK u st x hx with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
    · exact ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
    · refine ⟨hb_eq, by simpa using validPrincipals_corrupt S u.val (L.prins st) hVP, ?_,
        by simpa using hVS, by simpa using hSpkNotK,
        by simpa using cleanPeers_corrupt S P k u.val (L.prins st) (L.badPeers st) hClean⟩
      intro ⟨idx, e⟩ hp
      simp only [L.prins_putPrins, mem_corrupt_map] at hp
      rcases hp with ⟨e0, hmem, _⟩
      exact hNotK (idx, e0) hmem

theorem before_step_genSPK (P : Primitives) (k : Nat) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : St) (budget : Nat)
    (fL : R × St → ℝ≥0∞)
    (fR : Bytes → (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (hBefore : L.ActiveBefore P k st budget)
    (h_ih_before : ∀ out st' b', L.ActiveBefore P k st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) :
    probExpect ((L.realGenSPK P u j).run st) fL ≤
      probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget (L.stepGenSPK P u j ⟨st, k, P.sigPkGen sk,
            none⟩) []) (fR sk)) := by
  rcases hBefore with ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
  refine before_step_of_eq_real P k ((L.realGenSPK P u j).run st)
    (fun pk => L.stepGenSPK P u j ⟨st, k, pk, none⟩)
    (L.ActiveBefore P k) budget fL fR ?_ ?_ h_ih_before
  · intro pk
    unfold stepGenSPK
    by_cases hu : (u.val == k) = true
    · have hu_eq : u.val = k := beq_iff_eq.mp hu
      have hNone : (L.prins st).find? (fun (idx, _) => idx == u.val) = none := by
        rw [List.find?_eq_none]
        intro ⟨idx, e⟩ hmem hbeq
        exact hNotK (idx, e) hmem ((beq_iff_eq.mp hbeq).trans hu_eq)
      unfold realGenSPK
      by_cases hAny : (L.spks st).any (fun (key, _) => key == (u.val, j.val)) = true <;>
        simp [hu, hAny, hNone]
    · simp [hu]
  · intro x hx
    rcases L.mem_support_realGenSPK P u j st x hx with rfl | ⟨hAnyF, idx, uEntry, bEntry,
        bundleOut, hf, rfl⟩
    · exact ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
    · have hmem_p : (idx, uEntry) ∈ L.prins st := List.mem_of_find?_eq_some hf
      have hidx_eq : idx = u.val :=
        beq_iff_eq.mp (List.find?_some (p := fun x : Nat × PrincipalEntry => x.1 == u.val) hf)
      have hu_ne : u.val ≠ k := hidx_eq ▸ hNotK (idx, uEntry) hmem_p
      have hCons := (validSpkBundles_cons S u j bEntry (L.spks st) hVS hAnyF).1
      refine ⟨hb_eq, by simpa using hVP, by simpa using hNotK, by simpa using hCons, ?_,
          by simpa using hClean⟩
      intro e he
      simp only [L.spks_putSpks, List.mem_cons] at he
      rcases he with rfl | hmem
      · exact hu_ne
      · exact hSpkNotK e hmem

theorem before_step_initiate (P : Primitives) (k : Nat) (bundle : PreKeyBundleInput)
    (realInit : StateT St ProbComp R)
    (st : St) (budget : Nat)
    (fL : R × St → ℝ≥0∞)
    (fR : Bytes → (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (h_pres : ∀ x ∈ support (realInit.run st),
      L.prins x.2 = L.prins st ∧ L.spks x.2 = L.spks st ∧
      (L.badPeers x.2 = L.badPeers st ∨
       (∃ opkEntries, L.badPeers x.2 = bundle.ikB :: L.badPeers st ∧
         P.sigVerify (resolveSigPk P (L.prins st) bundle.ikB) (encodeEC bundle.spkB) bundle.spkSig =
             true ∧
         P.sigVerify (resolveSigPk P (L.prins st) bundle.ikB) (encodeKEM bundle.pqspkB)
             bundle.pqspkSig = true ∧
         (isHonestUncorruptedPeer P (L.prins st) bundle.ikB).isSome = true ∧
         !(let (spkHon, _, pqspkHon) :=
           checkBundleProvenance P (L.prins st) (L.spks st) opkEntries bundle; spkHon &&
               pqspkHon) = true)))
    (hBefore : L.ActiveBefore P k st budget)
    (h_ih_before : ∀ out st' b', L.ActiveBefore P k st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) :
    probExpect (realInit.run st) fL ≤
      probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget (L.stepInitiate P bundle realInit ⟨st, k,
            P.sigPkGen sk, none⟩) []) (fR sk)) := by
  rcases hBefore with ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
  refine before_step_of_eq_real P k (realInit.run st)
    (fun pk => L.stepInitiate P bundle realInit ⟨st, k, pk, none⟩)
    (L.ActiveBefore P k) budget fL fR ?_ ?_ h_ih_before
  · intro pk
    unfold stepInitiate
    simp [extractBundleForgery_eq_none_of_not_mem P k pk (L.prins st) (L.spks st) bundle hNotK]
  · intro x hx
    rcases h_pres x hx with ⟨hp, hs, hbp | ⟨_, hbp, _, _, hFresh, _⟩⟩
    · unfold ActiveBefore; rw [hp, hs, hbp]; exact ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
    · unfold ActiveBefore; rw [hp, hs, hbp]
      refine ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, ?_⟩
      exact cleanPeers_cons_of_before S P k (L.prins st) (L.badPeers st) bundle.ikB
        (fun p hp => ⟨hVP.1 p hp, hNotK p hp⟩) hClean hFresh

theorem before_step_other (P : Primitives) (k : Nat)
    (realOther : StateT St ProbComp R)
    (st : St) (budget : Nat)
    (fL : R × St → ℝ≥0∞)
    (fR : Bytes → (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (h_pres : ∀ x ∈ support (realOther.run st),
      L.prins x.2 = L.prins st ∧ SpksPreserved S (L.spks st) (L.spks x.2) ∧ L.badPeers x.2 =
          L.badPeers st)
    (hBefore : L.ActiveBefore P k st budget)
    (h_ih_before : ∀ out st' b', L.ActiveBefore P k st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) :
    probExpect (realOther.run st) fL ≤
      probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget (SigGameLens.stepOther realOther ⟨st, k,
            P.sigPkGen sk, none⟩) []) (fR sk)) := by
  rcases hBefore with ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
  refine before_step_of_eq_real P k (realOther.run st)
    (fun pk => SigGameLens.stepOther realOther ⟨st, k, pk, none⟩)
    (L.ActiveBefore P k) budget fL fR ?_ ?_ h_ih_before
  · intro pk; unfold stepOther; simp
  · intro x hx
    rcases h_pres x hx with ⟨hp, hs, hbp⟩
    unfold ActiveBefore; rw [hp, hbp]
    exact ⟨hb_eq, hVP, hNotK, hs.1 hVS, hs.2.1 k hSpkNotK, hClean⟩

@[simp]
theorem putPrins_eraseSk (k : Nat) (st : St) (p : List (Nat × PrincipalEntry)) :
    L.putPrins (L.eraseSk k st) p = L.putPrins st p := by
  simp [eraseSk]

/-! ### `ActiveAfter` Step Lemmas -/

theorem after_step_initPrin (P : Primitives) (k : Nat) (sk : Bytes) (u : Fin S.N_id)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (fL : R × St → ℝ≥0∞)
    (fR : (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (hAfter : L.ActiveAfter P k sk st s budget signedMsgs)
    (h_fL_zero : ∀ x, L.Safe P k x.2 → fL x = 0)
    (h_ih : ∀ out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect ((L.realInitPrin P u).run st) fL ≤
      probExpect (runSigStepSim P sk budget (L.stepInitPrin P u s) signedMsgs) fR := by
  rcases hAfter with ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
  refine after_step_of_erase P k sk budget (L.eraseSk k)
    ((L.realInitPrin P u).run st) (L.stepInitPrin P u ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩)
    signedMsgs (L.Safe P k) (L.ActiveAfter P k sk) fL fR ?_ ?_ h_fL_zero h_ih
  · unfold stepInitPrin
    by_cases hAny : (L.prins st).any (fun (idx, _) => idx == u.val) = true
    · unfold realInitPrin
      simp [hAny]
    · have hAnyF : (L.prins st).any (fun (idx, _) => idx == u.val) = false :=
        Bool.eq_false_iff.mpr hAny
      have huF : (u.val == k) = false := by
        apply Bool.eq_false_iff.mpr
        intro hu
        have hu_eq : k = u.val := (beq_iff_eq.mp hu).symm
        exact hAny (List.any_eq_true.mpr ⟨(k, ek), hek, beq_iff_eq.mpr hu_eq⟩)
      unfold realInitPrin
      simp [hAnyF, huF, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        StateT.run_set, pure_bind, erasePrinSk_cons_of_ne]
  · intro x hx
    refine Or.inr ?_
    rcases L.mem_support_realInitPrin P u st x hx with rfl | ⟨hAnyF, _, entry, rfl⟩
    · exact ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
    · have hCons := validPrincipals_cons S u entry (L.prins st) hVP hAnyF
      refine ⟨rfl, by simpa using hCons.1, ?_, by simpa using hVS, by simpa using hBudget,
        by simpa using hMsgs,
        by simpa using cleanPeers_cons_principal S P k u.val entry (L.prins st) (L.badPeers st)
            hClean⟩
      exact ⟨ek, by simp [hek], hsk, hpk, hcorr⟩

theorem after_step_corruptIK (P : Primitives) (k : Nat) (sk : Bytes) (u : Fin S.N_id)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (fL : R × St → ℝ≥0∞)
    (fR : (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (hAfter : L.ActiveAfter P k sk st s budget signedMsgs)
    (h_fL_zero : ∀ x, L.Safe P k x.2 → fL x = 0)
    (h_ih : ∀ out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect ((L.realCorruptIK u).run st) fL ≤
      probExpect (runSigStepSim P sk budget (L.stepCorruptIK u s) signedMsgs) fR := by
  rcases hAfter with ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
  by_cases hu : (u.val == k) = true
  · have hu_eq : u.val = k := beq_iff_eq.mp hu
    refine after_step_of_safe ((L.realCorruptIK u).run st)
      (runSigStepSim P sk budget (L.stepCorruptIK u ⟨L.eraseSk k st, k, P.sigPkGen sk,
          none⟩) signedMsgs)
      (L.Safe P k) fL fR ?_ h_fL_zero
    intro x hx
    have hFind : (L.prins st).find? (fun (i, _) => i == u.val) = some (k, ek) := by
      rw [hu_eq]
      exact find?_idx_eq_some_of_mem (L.prins st) hVP.2 k ek hek
    rcases L.mem_support_realCorruptIK u st x hx with ⟨hNone, _⟩ | ⟨_, _, _, rfl⟩
    · rw [hFind] at hNone; cases hNone
    · refine ⟨by simpa using validPrincipals_corrupt S u.val (L.prins st) hVP, ?_, ?_,
        by simpa using cleanPeers_corrupt S P k u.val (L.prins st) (L.badPeers st) hClean⟩
      · simp only [L.prins_putPrins]
        exact ⟨if k == u.val then { ek with corrupted := true } else ek,
          (mem_corrupt_map u.val k _ (L.prins st)).mpr ⟨ek, hek, rfl⟩⟩
      · intro e he
        simp only [L.prins_putPrins, mem_corrupt_map] at he
        rcases he with ⟨e0, _, rfl⟩
        have hku : (k == u.val) = true := beq_iff_eq.mpr hu_eq.symm
        simp [hku]
  · have huF : (u.val == k) = false := Bool.eq_false_iff.mpr hu
    have hkuF : (k == u.val) = false :=
      beq_eq_false_iff_ne.mpr (fun h => (beq_eq_false_iff_ne.mp huF) h.symm)
    refine after_step_of_erase P k sk budget (L.eraseSk k)
      ((L.realCorruptIK u).run st) (L.stepCorruptIK u ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩)
      signedMsgs (L.Safe P k) (L.ActiveAfter P k sk) fL fR ?_ ?_ h_fL_zero h_ih
    · unfold stepCorruptIK realCorruptIK
      simp only [huF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
        pure_bind, L.prins_eraseSk, find?_idx_erasePrinSk_of_ne k u.val (L.prins st) huF]
      cases (L.prins st).find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨idx, entry⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          L.putPrins_eraseSk, L.eraseSk_putPrins, corrupt_map_erasePrinSk]
    · intro x hx
      refine Or.inr ?_
      rcases L.mem_support_realCorruptIK u st x hx with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
      · exact ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
      · refine ⟨rfl, by simpa using validPrincipals_corrupt S u.val (L.prins st) hVP, ?_,
          by simpa using hVS, by simpa using hBudget, by simpa using hMsgs,
          by simpa using cleanPeers_corrupt S P k u.val (L.prins st) (L.badPeers st) hClean⟩
        simp only [L.prins_putPrins]
        refine ⟨ek, ?_, hsk, hpk, hcorr⟩
        rw [mem_corrupt_map]
        exact ⟨ek, hek, by simp [hkuF]⟩

theorem after_step_genSPK (P : Primitives) (k : Nat) (sk : Bytes) (u : Fin S.N_id) (j :
    Fin S.N_recv)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (fL : R × St → ℝ≥0∞)
    (fR : (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (hAfter : L.ActiveAfter P k sk st s budget signedMsgs)
    (h_fL_zero : ∀ x, L.Safe P k x.2 → fL x = 0)
    (h_ih : ∀ out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect ((L.realGenSPK P u j).run st) fL ≤
      probExpect (runSigStepSim P sk budget (L.stepGenSPK P u j s) signedMsgs) fR := by
  rcases hAfter with ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
  by_cases hu : (u.val == k) = true
  · have hu_eq : u.val = k := beq_iff_eq.mp hu
    by_cases hAny : (L.spks st).any (fun (key, _) => key == (u.val, j.val)) = true
    · unfold realGenSPK runSigStepSim stepGenSPK
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hu, L.spks_eraseSk, hAny,
        ↓reduceIte, StateT.run_pure, probExpect_pure]
      exact h_ih L.noneResp st ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩ budget signedMsgs
        ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
    · have hAnyF : (L.spks st).any (fun (key, _) => key == (u.val, j.val)) = false :=
        Bool.eq_false_iff.mpr hAny
      have hf : (L.prins st).find? (fun (idx, _) => idx == u.val) = some (k, ek) := by
        rw [hu_eq]
        exact find?_idx_eq_some_of_mem (L.prins st) hVP.2 k ek hek
      have hf_erase : (erasePrinSk k (L.prins st)).find? (fun (idx, _) => idx == u.val) =
          some (k, eraseEntrySk k k ek) := by
        rw [find?_idx_erasePrinSk, hf]; rfl
      let dummyB : SpkBundleEntry := {
        spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := []
      }
      have hLenLt : (L.spks st).length < S.N_spk_tot :=
        validSpkBundles_length_lt S u j dummyB (L.spks st) hVS hAnyF
      obtain ⟨b, rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by omega⟩
      have hL :
          probExpect ((L.realGenSPK P u j).run st) fL =
          probExpect sampleScalar32 (fun spkSk =>
            probExpect sampleRandom64 (fun rSpk =>
              probExpect (sampleKemKeyGen P) (fun pq =>
                probExpect sampleRandom64 (fun rPq =>
                  let spkPk := P.x25519Base spkSk
                  let spkSig := P.sigSign sk (encodeEC spkPk) rSpk
                  let pqspkSig := P.sigSign sk (encodeKEM pq.1) rPq
                  let bEntry : SpkBundleEntry := {
                    spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
                    pqspkSk := pq.2, pqspkPk := pq.1, pqspkSig := pqspkSig
                  }
                  let bundleOut : PreKeyBundleInput := {
                    ikB := ek.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
                    spkSig := spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
                    pqspkB := pq.1, pqspkSig := pqspkSig
                  }
                  fL (L.bundleResp bundleOut,
                      L.putSpks st (((u.val, j.val), bEntry) :: L.spks st)))))) := by
        unfold realGenSPK
        simp [StateT.run_bind, StateT.run_get, hAnyF, hf, hsk, StateT.run_monadLift,
          monadLift_self, StateT.run_set, pure_bind, probExpect_bind, probExpect_map]
      have hR :
          probExpect (runSigStepSim P sk (b + 1) (L.stepGenSPK P u j ⟨L.eraseSk k st, k,
              P.sigPkGen sk, none⟩) signedMsgs) fR =
          probExpect sampleScalar32 (fun spkSk =>
            probExpect sampleRandom64 (fun rSpk =>
              probExpect (sampleKemKeyGen P) (fun pq =>
                probExpect sampleRandom64 (fun rPq =>
                  let spkPk := P.x25519Base spkSk
                  let spkSig := P.sigSign sk (encodeEC spkPk) rSpk
                  let pqspkSig := P.sigSign sk (encodeKEM pq.1) rPq
                  let bEntry : SpkBundleEntry := {
                    spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
                    pqspkSk := pq.2, pqspkPk := pq.1, pqspkSig := pqspkSig
                  }
                  let bundleOut : PreKeyBundleInput := {
                    ikB := ek.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
                    spkSig := spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
                    pqspkB := pq.1, pqspkSig := pqspkSig
                  }
                  fR ((L.bundleResp bundleOut,
                       ⟨L.putSpks (L.eraseSk k st) (((u.val, j.val), bEntry) :: L.spks st), k,
                           P.sigPkGen sk, none⟩, b),
                      encodeKEM pq.1 :: encodeEC spkPk :: signedMsgs))))) := by
        unfold runSigStepSim stepGenSPK
        simp [hu, hAnyF, hf_erase, probExpect_bind, probExpect_map]
      rw [hL, hR]
      refine probExpect_mono_of_support sampleScalar32 _ _ (fun spkSk _ => ?_)
      refine probExpect_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
      refine probExpect_mono_of_support (sampleKemKeyGen P) _ _ (fun ⟨pqspkPk, pqspkSk⟩ _ => ?_)
      refine probExpect_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
      let spkPk := P.x25519Base spkSk
      let spkSig := P.sigSign sk (encodeEC spkPk) rSpk
      let pqspkSig := P.sigSign sk (encodeKEM pqspkPk) rPq
      let bEntry : SpkBundleEntry := {
        spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
        pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig
      }
      let bundleOut : PreKeyBundleInput := {
        ikB := ek.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
        spkSig := spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
        pqspkB := pqspkPk, pqspkSig := pqspkSig
      }
      let st' := L.putSpks st (((u.val, j.val), bEntry) :: L.spks st)
      have hCons := (validSpkBundles_cons S u j bEntry (L.spks st) hVS hAnyF).1
      apply h_ih (L.bundleResp bundleOut) st'
        ⟨L.putSpks (L.eraseSk k st) (((u.val, j.val), bEntry) :: L.spks st), k, P.sigPkGen sk, none⟩
        b (encodeKEM pqspkPk :: encodeEC spkPk :: signedMsgs)
      refine ⟨by simp [st'], by simpa [st'] using hVP, ⟨ek, by simpa [st'] using hek, hsk, hpk,
          hcorr⟩,
        by simpa [st'] using hCons, ?_, ?_, by simpa [st'] using hClean⟩
      · simp only [st', L.spks_putSpks, List.length_cons]
        omega
      · intro m hm
        simp only [st', L.spks_putSpks, hu_eq, bundleSignedMessages_cons_eq, List.mem_cons]
        simp only [List.mem_cons] at hm
        rcases hm with rfl | rfl | hm_old
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (hMsgs m hm_old))
  · have huF : (u.val == k) = false := Bool.eq_false_iff.mpr hu
    refine after_step_of_erase P k sk budget (L.eraseSk k)
      ((L.realGenSPK P u j).run st) (L.stepGenSPK P u j ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩)
      signedMsgs (L.Safe P k) (L.ActiveAfter P k sk) fL fR ?_ ?_ h_fL_zero h_ih
    · unfold stepGenSPK realGenSPK
      simp only [huF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
        pure_bind, L.spks_eraseSk, L.prins_eraseSk,
        find?_idx_erasePrinSk_of_ne k u.val (L.prins st) huF]
      by_cases hAny : (L.spks st).any (fun (key, _) => key == (u.val, j.val)) = true
      · simp [hAny]
      · have hAnyF : (L.spks st).any (fun (key, _) => key == (u.val, j.val)) = false :=
          Bool.eq_false_iff.mpr hAny
        simp only [hAnyF, Bool.false_eq_true, ↓reduceIte]
        cases (L.prins st).find? (fun (idx, _) => idx == u.val) with
        | none => simp
        | some p =>
          rcases p with ⟨idx, uEntry⟩
          simp [StateT.run_monadLift, monadLift_self, StateT.run_set]
    · intro x hx
      refine Or.inr ?_
      rcases L.mem_support_realGenSPK P u j st x hx with rfl | ⟨hAnyF, idx, uEntry, bEntry,
          bundleOut, _, rfl⟩
      · exact ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
      · have hCons := (validSpkBundles_cons S u j bEntry (L.spks st) hVS hAnyF).1
        refine ⟨rfl, by simpa using hVP, ⟨ek, by simp [hek], hsk, hpk, hcorr⟩,
          by simpa using hCons, ?_, ?_, by simpa using hClean⟩
        · simp only [L.spks_putSpks, List.length_cons]
          omega
        · intro m hm
          simp only [L.spks_putSpks,
              bundleSignedMessages_cons_of_ne k u.val j.val bEntry (L.spks st) huF]
          exact hMsgs m hm

theorem after_step_initiate (P : Primitives) (k : Nat) (sk : Bytes) (bundle : PreKeyBundleInput)
    (realInit : StateT St ProbComp R)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (fL : R × St → ℝ≥0∞)
    (fR : (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (h_erase : realInit.run (L.eraseSk k st) =
      (fun (out, st') => (out, L.eraseSk k st')) <$> realInit.run st)
    (h_pres : ∀ x ∈ support (realInit.run st),
      L.prins x.2 = L.prins st ∧ L.spks x.2 = L.spks st ∧
      (L.badPeers x.2 = L.badPeers st ∨
       (∃ opkEntries, L.badPeers x.2 = bundle.ikB :: L.badPeers st ∧
         P.sigVerify (resolveSigPk P (L.prins st) bundle.ikB) (encodeEC bundle.spkB) bundle.spkSig =
             true ∧
         P.sigVerify (resolveSigPk P (L.prins st) bundle.ikB) (encodeKEM bundle.pqspkB)
             bundle.pqspkSig = true ∧
         (isHonestUncorruptedPeer P (L.prins st) bundle.ikB).isSome = true ∧
         !(let (spkHon, _, pqspkHon) :=
           checkBundleProvenance P (L.prins st) (L.spks st) opkEntries bundle; spkHon &&
               pqspkHon) = true)))
    (hAfter : L.ActiveAfter P k sk st s budget signedMsgs)
    (h_fL_le : ∀ x, fL x ≤ 1)
    (h_fL_zero : ∀ x, L.Safe P k x.2 → fL x = 0)
    (h_fR_ge : ∀ y, SigWon P sk y.1.2.1 y.2 → 1 ≤ fR y)
    (h_ih : ∀ out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect (realInit.run st) fL ≤
      probExpect (runSigStepSim P sk budget (L.stepInitiate P bundle realInit s) signedMsgs) fR :=
          by
  rcases hAfter with ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
  cases hfg : extractBundleForgery P k (P.sigPkGen sk) (L.prins st) (L.spks st) bundle none with
  | some p =>
    rcases p with ⟨mStar, sigStar⟩
    have ⟨_, hver, hnotmem_bundle⟩ :=
      extractBundleForgery_valid_euf_cma P k (P.sigPkGen sk) (L.prins st) (L.spks st)
        bundle hfg
    have hnotmem_msgs : mStar ∉ signedMsgs :=
      fun hm => hnotmem_bundle (hMsgs mStar hm)
    refine after_step_of_won P sk budget (realInit.run st)
      (L.stepInitiate P bundle realInit ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩)
      signedMsgs fL fR ?_ h_fL_le h_fR_ge
    intro sr hsr
    unfold stepInitiate at hsr
    simp only [L.prins_eraseSk, L.spks_eraseSk, extractBundleForgery_erasePrinSk, hfg,
      support_bind, Set.mem_iUnion, exists_prop,
      support_pure, Set.mem_singleton_iff] at hsr
    rcases hsr with ⟨⟨out, gs'⟩, _, rfl⟩
    exact ⟨out, ⟨gs', k, P.sigPkGen sk, some (mStar, sigStar)⟩, rfl,
      ⟨mStar, sigStar, rfl, hver, hnotmem_msgs⟩⟩
  | none =>
    refine after_step_of_erase P k sk budget (L.eraseSk k)
      (realInit.run st) (L.stepInitiate P bundle realInit ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩)
      signedMsgs (L.Safe P k) (L.ActiveAfter P k sk) fL fR ?_ ?_ h_fL_zero h_ih
    · unfold stepInitiate
      simp [hfg, h_erase]
    · intro x hx
      refine Or.inr ?_
      rcases h_pres x hx with ⟨hp, hs, hbp | ⟨opkEntries, hbp, hSig1, hSig2, hFresh, hProv⟩⟩
      · unfold ActiveAfter
        rw [hp, hs, hbp]
        exact ⟨by simp [eraseSk, hp], hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
      · unfold ActiveAfter
        rw [hp, hs, hbp]
        refine ⟨by simp [eraseSk, hp], hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, ?_⟩
        exact cleanPeers_cons_of_extractBundleForgery_eq_none S P k sk
          (L.prins st) (L.spks st) opkEntries (L.badPeers st) bundle
          hVP ⟨ek, hek, hsk, hpk, hcorr⟩ hClean hfg hSig1 hSig2 hFresh hProv

theorem after_step_other (P : Primitives) (k : Nat) (sk : Bytes)
    (realOther : StateT St ProbComp R)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (fL : R × St → ℝ≥0∞)
    (fR : (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (h_erase : realOther.run (L.eraseSk k st) =
      (fun (out, st') => (out, L.eraseSk k st')) <$> realOther.run st)
    (h_pres : ∀ x ∈ support (realOther.run st),
      L.prins x.2 = L.prins st ∧ SpksPreserved S (L.spks st) (L.spks x.2) ∧ L.badPeers x.2 =
          L.badPeers st)
    (hAfter : L.ActiveAfter P k sk st s budget signedMsgs)
    (h_fL_zero : ∀ x, L.Safe P k x.2 → fL x = 0)
    (h_ih : ∀ out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect (realOther.run st) fL ≤
      probExpect (runSigStepSim P sk budget (SigGameLens.stepOther realOther s) signedMsgs) fR := by
  rcases hAfter with ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
  refine after_step_of_erase P k sk budget (L.eraseSk k)
    (realOther.run st) (SigGameLens.stepOther realOther ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩)
    signedMsgs (L.Safe P k) (L.ActiveAfter P k sk) fL fR ?_ ?_ h_fL_zero h_ih
  · unfold stepOther
    simp [h_erase]
  · intro x hx
    refine Or.inr ?_
    rcases h_pres x hx with ⟨hp, hs, hbp⟩
    unfold ActiveAfter
    rw [hp, hbp, hs.2.2.1]
    refine ⟨by simp [eraseSk, hp], hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hs.1 hVS, hBudget, ?_, hClean⟩
    intro m hm
    rw [hs.2.2.2 k]
    exact hMsgs m hm

end SigGameLens



def CommutesRel {St R : Type} (proj : St → St) (st : St)
    (m1 m2 : StateT St ProbComp R) : Prop :=
  (m1.run (proj st)) = Prod.map id proj <$> (m2.run st)

theorem CommutesRel.get_bind {St R : Type} (proj : St → St) (st : St)
    {f1 f2 : St → StateT St ProbComp R}
    (hf : CommutesRel proj st (f1 (proj st)) (f2 st)) :
    CommutesRel proj st (get >>= f1) (get >>= f2) := hf

theorem CommutesRel.pure {St R : Type} (proj : St → St) (st : St) (x : R) :
    CommutesRel proj st (Pure.pure x) (Pure.pure x) := by
  simp [CommutesRel]

theorem CommutesRel.liftM_bind {St R1 R2 : Type} (proj : St → St) (st : St)
    (mx : ProbComp R1) {f1 f2 : R1 → StateT St ProbComp R2}
    (hf : ∀ a, CommutesRel proj st (f1 a) (f2 a)) :
    CommutesRel proj st ((liftM mx : StateT St ProbComp R1) >>= f1)
      ((liftM mx : StateT St ProbComp R1) >>= f2) := by
  unfold CommutesRel at *
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
    bind_assoc, pure_bind, map_bind, hf]

theorem CommutesRel.set_bind {St R : Type} (proj : St → St) (st st1 st2 : St)
    {f1 f2 : PUnit → StateT St ProbComp R}
    (h : st1 = proj st2)
    (hf : CommutesRel proj st2 (f1 PUnit.unit) (f2 PUnit.unit)) :
    CommutesRel proj st (set st1 >>= f1) (set st2 >>= f2) := by
  unfold CommutesRel at *
  simp only [StateT.run_bind, StateT.run_set, pure_bind, h, hf]

theorem CommutesRel.ite {St R : Type} (proj : St → St) (st : St)
    (c : Prop) [Decidable c]
    {t1 t2 e1 e2 : StateT St ProbComp R}
    (ht : CommutesRel proj st t1 t2) (he : CommutesRel proj st e1 e2) :
    CommutesRel proj st (if c then t1 else e1) (if c then t2 else e2) := by
  by_cases hc : c <;> simp [hc, ht, he]

@[simp]
theorem isGameIdKey_erasePrinSk (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (pk : Bytes) :
    isGameIdKey P (erasePrinSk k principals) pk = isGameIdKey P principals pk := by
  unfold isGameIdKey
  exact findHonestPrincipal_erasePrinSk_isSome P k principals pk

@[simp]
theorem koskBundleOk_erasePrinSk (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    koskBundleOk P (erasePrinSk k principals) spkBundles opkEntries advKeys bundle =
      koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  unfold koskBundleOk
  rw [isGameIdKey_erasePrinSk]

@[simp]
theorem koskSenderOk_erasePrinSk (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes) :
    koskSenderOk P (erasePrinSk k principals) advKeys ikAPk =
      koskSenderOk P principals advKeys ikAPk := by
  unfold koskSenderOk
  rw [isGameIdKey_erasePrinSk]

def eraseKeyInd (S : Setup) (k : Nat) (st : KeyIndState S) : KeyIndState S :=
  { st with principals := erasePrinSk k st.principals }

theorem CommutesRel.recordKeyIndResp_bind (S : Setup) (P : Primitives) (k : Nat)
    (st : KeyIndState S) (r : KeyIndRespEntry S)
    {f1 f2 : PUnit → StateT (KeyIndState S) ProbComp KeyIndResponse}
    (hf : ∀ s', CommutesRel (eraseKeyInd S k) s' (f1 PUnit.unit) (f2 PUnit.unit)) :
    CommutesRel (eraseKeyInd S k) st (recordKeyIndResp S P r >>= f1) (recordKeyIndResp S P r >>= f2)
        := by
  unfold recordKeyIndResp
  simp only [bind_assoc]
  apply CommutesRel.get_bind
  dsimp only [eraseKeyInd]
  cases st.sessions.find? (fun s => keyIndPartner P s r) with
  | some s =>
    dsimp only; simp only [bind_assoc]
    rw [pure_bind, pure_bind]
    exact CommutesRel.set_bind (eraseKeyInd S k) st _ _ rfl (hf _)
  | none =>
    dsimp only; simp only [bind_assoc]
    exact CommutesRel.liftM_bind (eraseKeyInd S k) st sampleDRKey96 (fun _ =>
      CommutesRel.set_bind (eraseKeyInd S k) st _ _ rfl (hf _))

macro "prove_commutes_rel" : tactic =>
  `(tactic| repeat (first
    | apply CommutesRel.pure
    | (rw [pure_bind, pure_bind])
    | (apply CommutesRel.recordKeyIndResp_bind; intro _)
    | (apply CommutesRel.liftM_bind; intro _)
    | (apply CommutesRel.set_bind; rfl)
    | apply CommutesRel.ite
    | split))

theorem runKeyIndInitiate_commutes (useRo : Bool) (S : Setup) (P : Primitives) (k : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    CommutesRel (eraseKeyInd S k) st
      (runKeyIndInitiate useRo S P sid u bundle)
      (runKeyIndInitiate useRo S P sid u bundle) := by
  unfold runKeyIndInitiate
  apply CommutesRel.get_bind
  dsimp only [eraseKeyInd]
  rw [koskBundleOk_erasePrinSk, find?_idx_erasePrinSk]
  cases st.principals.find? (fun (idx, _) => idx == u.val) with
  | none => prove_commutes_rel
  | some p =>
    rcases p with ⟨idx, uEntry⟩
    dsimp only [Option.map]
    simp only [eraseEntrySk_secIKA0, eraseEntrySk_ikAPk, resolveSigPk_erasePrinSk,
      isHonestUncorruptedPeer_erasePrinSk, checkBundleProvenance_erasePrinSk,
      findHonestPrincipal_erasePrinSk]
    cases findHonestPrincipal P st.principals bundle.ikB <;>
        (dsimp only [Option.map]; prove_commutes_rel)

theorem pqxdhKeyIndImpl_other_commutes (useRo : Bool) (S : Setup) (P : Primitives) (k : Nat)
    (q : KeyIndQuery S) (st : KeyIndState S)
    (h_not_init : ∀ u, q ≠ .initPrin u)
    (h_not_corr : ∀ u, q ≠ .corruptIK u)
    (h_not_spk : ∀ u j, q ≠ .genSPK u j) :
    CommutesRel (eraseKeyInd S k) st
      (pqxdhKeyIndCachedImpl useRo S P q)
      (pqxdhKeyIndCachedImpl useRo S P q) := by
  cases q with
  | initPrin u => exact False.elim (h_not_init u rfl)
  | corruptIK u => exact False.elim (h_not_corr u rfl)
  | genSPK u j => exact False.elim (h_not_spk u j rfl)
  | genOPK u j o =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd]; prove_commutes_rel
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind
    by_cases h : bundle.opkB?.isNone = true
    · simp only [h, ↓reduceIte]; prove_commutes_rel
    · simp only [h, Bool.false_eq_true,
        ↓reduceIte]; exact runKeyIndInitiate_commutes useRo S P k _ u bundle st
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind
    by_cases h : bundle.opkB?.isSome = true
    · simp only [h, ↓reduceIte]; prove_commutes_rel
    · simp only [h, Bool.false_eq_true,
        ↓reduceIte]; exact runKeyIndInitiate_commutes useRo S P k _ u bundle st
  | acceptOPK u j o hdr =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd]
    rw [koskSenderOk_erasePrinSk, find?_idx_erasePrinSk]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => dsimp only [Option.map]; prove_commutes_rel
    | some p =>
      rcases p with ⟨idx, kEntry⟩
      dsimp only [Option.map]
      simp only [eraseEntrySk_secIKA0, eraseEntrySk_ikAPk, findHonestPrincipal_erasePrinSk]
      cases findHonestPrincipal P st.principals hdr.ikAPk <;>
        (dsimp only [Option.map]; prove_commutes_rel)
  | acceptNoOPK u j l hdr =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd]
    rw [koskSenderOk_erasePrinSk, find?_idx_erasePrinSk]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => dsimp only [Option.map]; prove_commutes_rel
    | some p =>
      rcases p with ⟨idx, kEntry⟩
      dsimp only [Option.map]
      simp only [eraseEntrySk_secIKA0, eraseEntrySk_ikAPk, findHonestPrincipal_erasePrinSk]
      cases findHonestPrincipal P st.principals hdr.ikAPk <;>
        (dsimp only [Option.map]; prove_commutes_rel)
  | testSession sid =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd, isKeyIndSessionTestable]; prove_commutes_rel
  | revealSessionKey sid =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd]; prove_commutes_rel
  | roQuery secrets =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd]; prove_commutes_rel
  | revealDhSecrets =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd]
    simp only [map_secIKA0_erasePrinSk]; prove_commutes_rel
  | registerKey sk =>
    unfold pqxdhKeyIndCachedImpl; apply CommutesRel.get_bind; dsimp only [eraseKeyInd];
        prove_commutes_rel
  | revealSpkSk u j =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [eraseKeyInd]; prove_commutes_rel


def SatisfiesAt {St R : Type} (Q : St → Prop) (st : St) (m : StateT St ProbComp R) : Prop :=
  ∀ x ∈ support (m.run st), Q x.2

theorem SatisfiesAt.pure {St R : Type} (Q : St → Prop) (st : St) (x : R) (h0 : Q st) :
    SatisfiesAt Q st (pure x) := by
  intro y hy
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
  subst hy; exact h0

theorem SatisfiesAt.get_bind {St R : Type} (Q : St → Prop) (st : St)
    {f : St → StateT St ProbComp R} (hf : SatisfiesAt Q st (f st)) :
    SatisfiesAt Q st (get >>= f) := hf

theorem SatisfiesAt.liftM_bind {St R1 R2 : Type} (Q : St → Prop) (st : St)
    (mx : ProbComp R1) {f : R1 → StateT St ProbComp R2}
    (hf : ∀ a, SatisfiesAt Q st (f a)) :
    SatisfiesAt Q st ((liftM mx : StateT St ProbComp R1) >>= f) := by
  intro x hx
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨a, _, h2⟩
  exact hf a x h2

theorem SatisfiesAt.ite_return {St R : Type} (Q : St → Prop) (st : St)
    (c : Bool) (x : R) {e : StateT St ProbComp R}
    (h0 : Q st) (he : c = false → SatisfiesAt Q st e) :
    SatisfiesAt Q st (if c = true then Pure.pure x else e) := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte]; exact SatisfiesAt.pure Q st x h0
  · have hcF : c = false := Bool.eq_false_iff.mpr hc
    simp only [hcF, Bool.false_eq_true, ↓reduceIte]
    exact he hcF

theorem SatisfiesAt.set_of_pres {St R : Type} (Q : St → Prop) (st st' : St)
    {f : PUnit → StateT St ProbComp R}
    (h_st' : Q st')
    (hf : ∀ x ∈ support ((f PUnit.unit).run st'), x.2 = st') :
    SatisfiesAt Q st (set st' >>= f) := by
  intro x hx
  simp only [StateT.run_bind, StateT.run_set, pure_bind] at hx
  rw [hf x hx]
  exact h_st'

def badPeersKeyInd {S : Setup} (st : KeyIndState S) : List Bytes :=
  (st.sessions.filter (fun s => s.fresh && (!s.spkHonest ||
      !s.pqspkHonest))).map (fun s => s.peerIkPk)

def InitPostKeyInd {S : Setup} (P : Primitives) (bundle : PreKeyBundleInput) (st st' :
    KeyIndState S) : Prop :=
  st'.principals = st.principals ∧ st'.spkBundles = st.spkBundles ∧
  (badPeersKeyInd st' = badPeersKeyInd st ∨
   (∃ opkEntries, badPeersKeyInd st' = bundle.ikB :: badPeersKeyInd st ∧
     P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB) bundle.spkSig =
         true ∧
     P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB) bundle.pqspkSig
         = true ∧
     (isHonestUncorruptedPeer P st.principals bundle.ikB).isSome = true ∧
     !(let (spkHon, _, pqspkHon) :=
       checkBundleProvenance P st.principals st.spkBundles opkEntries bundle; spkHon &&
           pqspkHon) = true))

theorem initPostKeyInd_refl {S : Setup} (P : Primitives) (bundle : PreKeyBundleInput) (st :
    KeyIndState S) :
    InitPostKeyInd P bundle st st :=
  ⟨rfl, rfl, Or.inl rfl⟩

theorem initPostKeyInd_cons_session {S : Setup} (P : Primitives) (bundle : PreKeyBundleInput)
    (st : KeyIndState S) (sess : KeyIndInitiatorEntry S) (roCache' : List (Bytes × DRKey))
    (h_peer : sess.peerIkPk = bundle.ikB)
    (h_fresh : sess.fresh = (isHonestUncorruptedPeer P st.principals bundle.ikB).isSome)
    (h_spk : sess.spkHonest =
        (checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle).1)
    (h_pqspk : sess.pqspkHonest =
        (checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle).2.2)
    (h_sig :
        (!(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB)
        bundle.spkSig &&
       P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
           bundle.pqspkSig)) = false) :
    InitPostKeyInd P bundle st { st with
                                 sessions := sess :: st.sessions, roCache := roCache' } := by
  refine ⟨rfl, rfl, ?_⟩
  unfold badPeersKeyInd
  dsimp only
  rw [List.filter_cons]
  by_cases hbad : (sess.fresh && (!sess.spkHonest || !sess.pqspkHonest)) = true
  · right
    have hmap : List.map (fun s => s.peerIkPk)
        (if (sess.fresh && (!sess.spkHonest || !sess.pqspkHonest)) = true then
          sess :: List.filter (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) st.sessions
        else List.filter (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) st.sessions) =
        bundle.ikB :: List.map (fun s => s.peerIkPk)
          (List.filter (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) st.sessions) := by
      simp [hbad, h_peer]
    simp only [Bool.not_eq_false', Bool.and_eq_true] at h_sig
    simp only [Bool.and_eq_true, h_fresh, h_spk, h_pqspk, ← Bool.not_and] at hbad
    exact ⟨st.opkEntries, hmap, h_sig.1, h_sig.2, hbad.1, by simpa using hbad.2⟩
  · left
    simp [hbad]

theorem runKeyIndInitiate_pres (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    SatisfiesAt (InitPostKeyInd P bundle st) st (runKeyIndInitiate useRo S P sid u bundle) := by
  have h0 := initPostKeyInd_refl P bundle st
  unfold runKeyIndInitiate
  apply SatisfiesAt.get_bind
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  split
  · apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    apply SatisfiesAt.liftM_bind; intro _
    apply SatisfiesAt.liftM_bind; intro _
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro h_sig
    split
    · apply SatisfiesAt.liftM_bind; intro _
      dsimp only
      split
      · rw [pure_bind]
        refine SatisfiesAt.set_of_pres _ _ _ (initPostKeyInd_cons_session P bundle st _ _ rfl rfl
            rfl rfl h_sig) ?_
        intro x hx; split at hx <;> simp at hx <;> rw [hx]
      · apply SatisfiesAt.liftM_bind; intro _
        refine SatisfiesAt.set_of_pres _ _ _ (initPostKeyInd_cons_session P bundle st _ _ rfl rfl
            rfl rfl h_sig) ?_
        intro x hx; split at hx <;> simp at hx <;> rw [hx]
    · exact SatisfiesAt.pure _ _ _ h0
  · exact SatisfiesAt.pure _ _ _ h0

theorem badPeersKeyInd_map_tested {S : Setup} (sessions : List (KeyIndInitiatorEntry S)) (sid :
    SessionId S) :
    ((sessions.map (fun s => if s.sid == sid then { s with tested := true } else s)).filter
      (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest))).map (fun s => s.peerIkPk) =
    (sessions.filter (fun s => s.fresh && (!s.spkHonest ||
        !s.pqspkHonest))).map (fun s => s.peerIkPk) := by
  induction sessions with
  | nil => rfl
  | cons s tl ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    have hcond : (if s.sid == sid then { s with tested := true } else s).fresh = s.fresh ∧
        (if s.sid == sid then { s with tested := true } else s).spkHonest = s.spkHonest ∧
        (if s.sid == sid then { s with tested := true } else s).pqspkHonest = s.pqspkHonest ∧
        (if s.sid == sid then { s with tested := true } else s).peerIkPk = s.peerIkPk := by
      cases s.sid == sid <;> exact ⟨rfl, rfl, rfl, rfl⟩
    rw [hcond.1, hcond.2.1, hcond.2.2.1]
    cases hf : (s.fresh && (!s.spkHonest || !s.pqspkHonest))
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · simp only [↓reduceIte, List.map_cons, hcond.2.2.2, ih]

theorem badPeersKeyInd_map_revealed {S : Setup} (sessions : List (KeyIndInitiatorEntry S)) (sid :
    SessionId S) :
    ((sessions.map (fun s => if s.sid == sid then { s with revealed := true } else s)).filter
      (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest))).map (fun s => s.peerIkPk) =
    (sessions.filter (fun s => s.fresh && (!s.spkHonest ||
        !s.pqspkHonest))).map (fun s => s.peerIkPk) := by
  induction sessions with
  | nil => rfl
  | cons s tl ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    have hcond : (if s.sid == sid then { s with revealed := true } else s).fresh = s.fresh ∧
        (if s.sid == sid then { s with revealed := true } else s).spkHonest = s.spkHonest ∧
        (if s.sid == sid then { s with revealed := true } else s).pqspkHonest = s.pqspkHonest ∧
        (if s.sid == sid then { s with revealed := true } else s).peerIkPk = s.peerIkPk := by
      cases s.sid == sid <;> exact ⟨rfl, rfl, rfl, rfl⟩
    rw [hcond.1, hcond.2.1, hcond.2.2.1]
    cases hf : (s.fresh && (!s.spkHonest || !s.pqspkHonest))
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · simp only [↓reduceIte, List.map_cons, hcond.2.2.2, ih]

macro "prove_preserves_at" : tactic =>
  `(tactic| repeat (first
    | with_reducible apply PreservesAt.pure
    | (rw [pure_bind])
    | with_reducible apply PreservesAt.get_bind
    | (with_reducible apply PreservesAt.liftM_bind; intro _)
    | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
    | ((with_reducible apply PreservesAt.set_bind); rfl)
    | (split; try dsimp only)))

theorem pqxdhKeyIndImpl_other_pres (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S)
    (h_not_init : ∀ u, q ≠ .initPrin u)
    (h_not_corr : ∀ u, q ≠ .corruptIK u)
    (h_not_spk : ∀ u j, q ≠ .genSPK u j)
    (h_not_iopk : ∀ u i b, q ≠ .initiateOPK u i b)
    (h_not_inoopk : ∀ u i b, q ≠ .initiateNoOPK u i b) :
    ∀ x ∈ support ((pqxdhKeyIndCachedImpl useRo S P q).run st),
      x.2.principals = st.principals ∧ SpksPreserved S st.spkBundles x.2.spkBundles ∧
      badPeersKeyInd x.2 = badPeersKeyInd st := by
  let proj := fun s : KeyIndState S => (s.principals, s.spkBundles, s.sessions)
  have h_from_proj : ∀ m : StateT (KeyIndState S) ProbComp KeyIndResponse,
      PreservesAt proj st m →
      ∀ x ∈ support (m.run st),
        x.2.principals = st.principals ∧ SpksPreserved S st.spkBundles x.2.spkBundles ∧
        badPeersKeyInd x.2 = badPeersKeyInd st := by
    intro m hP x hx
    have h := hP x hx
    have hs : x.2.sessions = st.sessions := congrArg (Prod.snd ∘ Prod.snd) h
    exact ⟨congrArg Prod.fst h, spksPreserved_of_eq S (congrArg (Prod.fst ∘ Prod.snd) h),
        by unfold badPeersKeyInd; rw [hs]⟩
  cases q with
  | initPrin u => exact False.elim (h_not_init u rfl)
  | corruptIK u => exact False.elim (h_not_corr u rfl)
  | genSPK u j => exact False.elim (h_not_spk u j rfl)
  | initiateOPK u i b => exact False.elim (h_not_iopk u i b rfl)
  | initiateNoOPK u i b => exact False.elim (h_not_inoopk u i b rfl)
  | testSession sid =>
    have hP : PreservesAt (fun s => (s.principals, s.spkBundles, badPeersKeyInd s)) st
        (pqxdhKeyIndCachedImpl useRo S P (.testSession sid)) := by
      unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only
      apply PreservesAt.get_bind
      split
      · apply PreservesAt.pure
      · split
        · apply PreservesAt.set_bind
          · exact Prod.ext rfl (Prod.ext rfl (badPeersKeyInd_map_tested st.sessions sid))
          · apply PreservesAt.pure
        · split
          · apply PreservesAt.pure
          · apply PreservesAt.set_bind
            · rfl
            · apply PreservesAt.pure
    intro x hx; have h := hP x hx
    exact ⟨congrArg Prod.fst h, spksPreserved_of_eq S (congrArg (Prod.fst ∘ Prod.snd) h),
        congrArg (Prod.snd ∘ Prod.snd) h⟩
  | revealSessionKey sid =>
    have hP : PreservesAt (fun s => (s.principals, s.spkBundles, badPeersKeyInd s)) st
        (pqxdhKeyIndCachedImpl useRo S P (.revealSessionKey sid)) := by
      unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only
      apply PreservesAt.get_bind
      split
      · split
        · apply PreservesAt.pure
        · apply PreservesAt.set_bind
          · exact Prod.ext rfl (Prod.ext rfl (badPeersKeyInd_map_revealed st.sessions sid))
          · apply PreservesAt.pure
      · split
        · apply PreservesAt.pure
        · split
          · apply PreservesAt.pure
          · apply PreservesAt.set_bind
            · rfl
            · apply PreservesAt.pure
    intro x hx; have h := hP x hx
    exact ⟨congrArg Prod.fst h, spksPreserved_of_eq S (congrArg (Prod.fst ∘ Prod.snd) h),
        congrArg (Prod.snd ∘ Prod.snd) h⟩
  | genOPK u j o =>
    apply h_from_proj; unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only; prove_preserves_at
  | acceptOPK u j o hdr =>
    apply h_from_proj; unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only; prove_preserves_at
  | acceptNoOPK u j l hdr =>
    apply h_from_proj; unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only; prove_preserves_at
  | roQuery secrets =>
    apply h_from_proj; unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only; prove_preserves_at
  | revealDhSecrets =>
    apply h_from_proj; unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only; prove_preserves_at
  | registerKey sk =>
    apply h_from_proj; unfold pqxdhKeyIndCachedImpl; dsimp only; prove_preserves_at
  | revealSpkSk u j =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      intro x hx
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨rfl, spksPreserved_of_eq S rfl, rfl⟩
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      dsimp only
      intro x hx
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, spksPreserved_map_revealed S P (u.val, j.val) st.spkBundles, rfl⟩

def keyIndSigLens (S : Setup) : SigGameLens S (KeyIndState S) KeyIndResponse where
  prins        := fun st => st.principals
  putPrins     := fun st p => { st with principals := p }
  spks         := fun st => st.spkBundles
  putSpks      := fun st s => { st with spkBundles := s }
  badPeers     := badPeersKeyInd
  noneResp     := .noneResp
  initPrinResp := .initPrinResp
  corrResp     := .corrResp
  bundleResp   := .bundleResp
  prins_putPrins    := fun _ _ => rfl
  spks_putPrins     := fun _ _ => rfl
  badPeers_putPrins := fun _ _ => rfl
  putPrins_putPrins := fun _ _ _ => rfl
  prins_putSpks     := fun _ _ => rfl
  spks_putSpks      := fun _ _ => rfl
  badPeers_putSpks  := fun _ _ => rfl
  putPrins_putSpks  := fun _ _ _ => rfl

noncomputable def stepKeyIndForSig (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (s : SigReductionState (KeyIndState S)) :
    ProbComp (SigStepResult (SigReductionState (KeyIndState S)) KeyIndResponse) :=
  if s.forgery.isSome then
    pure (.done .noneResp s)
  else
    match q with
    | .initPrin u => (keyIndSigLens S).stepInitPrin P u s
    | .corruptIK u => (keyIndSigLens S).stepCorruptIK u s
    | .genSPK u j => (keyIndSigLens S).stepGenSPK P u j s
    | .initiateOPK u i bundle =>
      (keyIndSigLens S).stepInitiate P bundle (pqxdhKeyIndCachedImpl useRo S P (.initiateOPK u i
          bundle)) s
    | .initiateNoOPK u i bundle =>
      (keyIndSigLens S).stepInitiate P bundle (pqxdhKeyIndCachedImpl useRo S P (.initiateNoOPK u i
          bundle)) s
    | q_other =>
      SigGameLens.stepOther (pqxdhKeyIndCachedImpl useRo S P q_other) s


theorem primBounded_stepKeyIndForSigPrim (useRo : Bool) (S : Setup)
    (q : KeyIndQuery S) (s : SigReductionState (KeyIndState S)) :
    PrimBounded (stepKeyIndForSigPrim useRo S q s) (S.N_dh * 20 + S.N_sess_tot * 8 + 16) := by
  unfold stepKeyIndForSigPrim
  split_ifs
  · exact primBounded_pure'
  · cases q with
    | initPrin u =>
      dsimp only
      split_ifs
      · exact primBounded_pure'
      · refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
        exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
      · exact primBounded_bind_le 0 (primBounded_pqxdhKeyIndImplPrim useRo S (.initPrin u)
          s.gameState)
          (fun _ => primBounded_pure')
    | corruptIK u =>
      dsimp only
      split_ifs
      · cases s.gameState.principals.find? (fun (idx,
          _) => idx == u.val) <;> exact primBounded_pure'
      · exact primBounded_bind_le 0 (primBounded_pqxdhKeyIndImplPrim useRo S (.corruptIK u)
          s.gameState)
          (fun _ => primBounded_pure')
    | genSPK u j =>
      dsimp only
      split_ifs
      · exact primBounded_pure'
      · cases s.gameState.principals.find? (fun (idx, _) => idx == u.val) with
        | none => exact primBounded_pure'
        | some p =>
          rcases p with ⟨_, uEntry⟩
          dsimp only
          refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
          exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
      · exact primBounded_bind_le 0 (primBounded_pqxdhKeyIndImplPrim useRo S (.genSPK u j)
          s.gameState)
          (fun _ => primBounded_pure')
    | initiateOPK u i bundle =>
      dsimp only
      refine primBounded_bind_le (S.N_dh * 18 + S.N_sess_tot * 8 + 14)
        (primBounded_extractBundleForgeryPrim S s.targetParty s.targetPk s.gameState.principals
            s.gameState.spkBundles bundle s.forgery)
        (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_pqxdhKeyIndImplPrim useRo S (.initiateOPK u i bundle)
          s.gameState)
        (fun _ => primBounded_pure')
    | initiateNoOPK u i bundle =>
      dsimp only
      refine primBounded_bind_le (S.N_dh * 18 + S.N_sess_tot * 8 + 14)
        (primBounded_extractBundleForgeryPrim S s.targetParty s.targetPk s.gameState.principals
            s.gameState.spkBundles bundle s.forgery)
        (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_pqxdhKeyIndImplPrim useRo S (.initiateNoOPK u i
          bundle) s.gameState)
        (fun _ => primBounded_pure')
    | genOPK u j o
    | acceptOPK u j o _
    | acceptNoOPK u j o _
    | testSession _
    | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
      dsimp only
      exact primBounded_bind_le 0 (primBounded_pqxdhKeyIndImplPrim useRo S _ s.gameState)
        (fun _ => primBounded_pure')

theorem evalStepPrim_stepKeyIndForSigPrim (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (s : SigReductionState (KeyIndState S))
    (hPrin : s.gameState.principals.length ≤ S.N_dh)
    (hSpk : s.gameState.spkBundles.length ≤ S.N_dh)
    (hOpk : s.gameState.opkEntries.length ≤ S.N_dh)
    (hSess : s.gameState.sessions.length ≤ S.N_dh)
    (hResp : s.gameState.respSessions.length ≤ S.N_sess_tot)
    (hAdv : ValidAdvKeysPow8 P s.gameState.advKeys) :
    evalStepPrim P (stepKeyIndForSigPrim useRo S) q s =
      stepKeyIndForSig useRo S P q s := by
  unfold evalStepPrim stepKeyIndForSigPrim stepKeyIndForSig
  split_ifs with hSome
  · rfl
  · cases q with
    | initPrin u =>
      dsimp only [SigGameLens.stepInitPrin, keyIndSigLens]
      split_ifs
      · rfl
      · simp only [simulateQ_bind, simulateQ_embedUnif,
          simulateQ_pure, map_bind, map_pure, SigStepResultPrim.toProbComp]
        rfl
      · rw [simulateQ_bind, map_bind,
          simulateQ_pqxdhKeyIndImplPrim useRo S P hP (.initPrin u) s.gameState hPrin hSpk hOpk hSess
              hResp hAdv]
        rfl
    | corruptIK u =>
      dsimp only [SigGameLens.stepCorruptIK, keyIndSigLens]
      split_ifs
      · cases s.gameState.principals.find? (fun (idx, _) => idx == u.val) <;> rfl
      · rw [simulateQ_bind, map_bind,
          simulateQ_pqxdhKeyIndImplPrim useRo S P hP (.corruptIK u) s.gameState hPrin hSpk hOpk
              hSess hResp hAdv]
        rfl
    | genSPK u j =>
      dsimp only [SigGameLens.stepGenSPK, keyIndSigLens]
      split_ifs
      · rfl
      · cases s.gameState.principals.find? (fun (idx, _) => idx == u.val) with
        | none => rfl
        | some p =>
          rcases p with ⟨_, uEntry⟩
          dsimp only
          simp only [simulateQ_bind, simulateQ_embedUnif,
            simulateQ_pure, map_bind, map_pure, SigStepResultPrim.toProbComp]
          rfl
      · rw [simulateQ_bind, map_bind,
          simulateQ_pqxdhKeyIndImplPrim useRo S P hP (.genSPK u j) s.gameState hPrin hSpk hOpk hSess
              hResp hAdv]
        rfl
    | initiateOPK u i bundle =>
      dsimp only [SigGameLens.stepInitiate, keyIndSigLens]
      rw [simulateQ_bind, map_bind,
        simulateQ_extractBundleForgeryPrim S P s.targetParty s.targetPk s.gameState.principals
            s.gameState.spkBundles bundle s.forgery hPrin,
        pure_bind, simulateQ_bind, map_bind,
        simulateQ_pqxdhKeyIndImplPrim useRo S P hP (.initiateOPK u i bundle) s.gameState hPrin hSpk
            hOpk hSess hResp hAdv]
      simp [SigStepResultPrim.toProbComp]
    | initiateNoOPK u i bundle =>
      dsimp only [SigGameLens.stepInitiate, keyIndSigLens]
      rw [simulateQ_bind, map_bind,
        simulateQ_extractBundleForgeryPrim S P s.targetParty s.targetPk s.gameState.principals
            s.gameState.spkBundles bundle s.forgery hPrin,
        pure_bind, simulateQ_bind, map_bind,
        simulateQ_pqxdhKeyIndImplPrim useRo S P hP (.initiateNoOPK u i bundle) s.gameState hPrin
            hSpk hOpk hSess hResp hAdv]
      simp [SigStepResultPrim.toProbComp]
    | genOPK u j o
    | acceptOPK u j o _
    | acceptNoOPK u j o _
    | testSession _
    | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
      dsimp only [SigGameLens.stepOther]
      rw [simulateQ_bind, map_bind,
        simulateQ_pqxdhKeyIndImplPrim useRo S P hP _ s.gameState hPrin hSpk hOpk hSess hResp hAdv]
      simp [SigStepResultPrim.toProbComp]


theorem validTaggedPks_length_le {N : Nat} {tagged : List (Nat × Bytes)}
    (hV : ValidTaggedPks N tagged) : tagged.length ≤ N := by
  have hsub : (tagged.map Prod.fst).Subperm (List.range N) :=
    hV.2.subperm (fun y hy => by
      rw [List.mem_map] at hy
      rcases hy with ⟨p, hp, rfl⟩
      exact List.mem_range.mpr (hV.1 p hp))
  have hle := hsub.length_le
  simpa using hle

theorem validKeyIndEc_lengths_le (S : Setup) (P : Primitives) (st : KeyIndState S)
    (hV : ValidKeyIndEc S st) :
    st.principals.length ≤ S.N_dh ∧
    st.spkBundles.length ≤ S.N_dh ∧
    st.opkEntries.length ≤ S.N_dh ∧
    st.sessions.length ≤ S.N_dh := by
  have hTag := validTaggedPks_ecTaggedFromLists S P
    st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st) hV
  have hLen := validTaggedPks_length_le hTag
  unfold ecTaggedFromLists sessPksKeyInd at hLen
  simp only [List.length_append, List.length_map] at hLen
  exact ⟨by omega, by omega, by omega, by omega⟩

@[simp]
theorem erasePrinSk_length (k : Nat) (principals : List (Nat × PrincipalEntry)) :
    (erasePrinSk k principals).length = principals.length := by
  unfold erasePrinSk
  simp

theorem runKeyIndInitiate_validKeyIndEc (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid) (u : Fin S.N_id) (bundle :
        PreKeyBundleInput)
    (st : KeyIndState S) (hV : ValidKeyIndEc S st) :
    ∀ x ∈ support ((runKeyIndInitiate useRo S P sid u bundle).run st), ValidKeyIndEc S x.2 := by
  rcases hV with ⟨hVP, hVS, hVO, hVSess⟩
  unfold runKeyIndInitiate; dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hFresh : st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hFresh' : ((sessPksKeyInd S st).map Prod.fst).any (fun s => s == sid) = false := by
      simpa [sessPksKeyInd, List.any_map, Function.comp_def] using hFresh
    have hCons :=
        validSessionIds_cons S sid ((sessPksKeyInd S st).map Prod.fst) hSend hVSess hFresh'
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      cases !(koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle)
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind]
        cases hSig :
            !(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB)
            bundle.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                bundle.pqspkSig)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨ekASk, _, kemCoins, _, hx⟩
          cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            rw [hEnc] at hx
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact ⟨hVP, hVS, hVO, hVSess⟩
          | some val =>
            rcases val with ⟨ss, kemCt⟩
            rw [hEnc] at hx
            dsimp only at hx
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
              bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨⟨drKeyReal, roCache'⟩, _, hx⟩
            split at hx <;>
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
            swap; rcases hx with ⟨drKeyRand, _, hx⟩; all_goals
            have hx_st : x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
                x.2.opkEntries = st.opkEntries ∧
                (sessPksKeyInd S x.2).map Prod.fst = sid :: (sessPksKeyInd S st).map Prod.fst := by
              cases hHon : findHonestPrincipal P st.principals bundle.ikB <;> (
                rw [hHon] at hx
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
                subst hx
                simp [sessPksKeyInd])
            rcases hx_st with ⟨hp1, hp2, hp3, hp4⟩
            exact ⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hCons.1⟩
        · simp only [↓reduceIte, StateT.run_pure]
          intro x hx
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨_, _, _, _, rfl⟩
          exact ⟨hVP, hVS, hVO, hVSess⟩
      · simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  · simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]

theorem pqxdhKeyIndImpl_validKeyIndEc_step (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : ValidKeyIndEc S st) :
    ∀ x ∈ support ((pqxdhKeyIndImpl useRo S P q).run st), ValidKeyIndEc S x.2 := by
  let proj := fun s : KeyIndState S => (s.principals, s.spkBundles, s.opkEntries, s.sessions)
  have h_from_proj : ∀ s : KeyIndState S, proj s = proj st → ValidKeyIndEc S s := by
    intro s hs
    have hp : s.principals = st.principals := congrArg Prod.fst hs
    have hsb : s.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) hs
    have hop : s.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hs
    have hss : s.sessions = st.sessions := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hs
    unfold ValidKeyIndEc ValidEcLists sessPksKeyInd at hV ⊢; rw [hp, hsb, hop, hss]; exact hV
  rcases hV with ⟨hVP, hVS, hVO, hVSess⟩
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨secIKA0, _, secIKAsign, _, rfl⟩
      exact ⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hVSess⟩
    · simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | corruptIK u =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      have h_corr := validPrincipals_map_corrupted S P u.val st.principals hVP
      intro x hx
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨h_corr.1, hVS, hVO, hVSess⟩
  | genSPK u j =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        exact ⟨hVP, (validSpkBundles_cons S u j _ st.spkBundles hVS hFresh).1, hVO, hVSess⟩
    · simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | genOPK u j o =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨opkSk, _, rfl⟩
      exact ⟨hVP, hVS, (validOpkEntries_cons S u j o _ st.opkEntries hVO hFresh).1, hVSess⟩
    · simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_validKeyIndEc useRo S P (.sendOPK u i) trivial u bundle st ⟨hVP, hVS,
          hVO, hVSess⟩
    · simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_validKeyIndEc useRo S P (.sendNoOPK u i) trivial u bundle st ⟨hVP,
          hVS, hVO, hVSess⟩
    · simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | acceptOPK k j o hdr =>
    let projOpk := fun s : KeyIndState S =>
      (s.principals, s.spkBundles, s.opkEntries.map Prod.fst, s.sessions)
    have h_step : ∀ (s : KeyIndState S) u t rc,
        projOpk { s with
          opkEntries := s.opkEntries.map (fun (idx, e) =>
            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
          usedRecvOPK := u, seenKyberBaseKeys := t, roCache := rc } = projOpk s := by
      intro s u t rc
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
      dsimp only [projOpk]
      rw [List.map_map]
      refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projOpk st (pqxdhKeyIndImpl useRo S P (.acceptOPK k j o hdr)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _ _ _ _)
        | split)
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp4 : x.2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp5 : sessPksKeyInd S x.2 = sessPksKeyInd S st := by
      have hsess : x.2.sessions = st.sessions :=
        congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
      unfold sessPksKeyInd; rw [hsess]
    refine ⟨hp1 ▸ hVP, hp2 ▸ hVS, ⟨?_, ?_⟩, hp5 ▸ hVSess⟩
    · intro e he
      have he_fst : e.1 ∈ st.opkEntries.map Prod.fst := by
        rw [← hp4]; exact List.mem_map_of_mem he
      rw [List.mem_map] at he_fst
      rcases he_fst with ⟨e', he', heq⟩
      rw [← heq]; exact hVO.1 e' he'
    · have h_slot : x.2.opkEntries.map (fun e => ecOpkSlotIdx S e.1) =
          st.opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hp4
      rw [h_slot]; exact hVO.2
  | acceptNoOPK k j l hdr =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.acceptNoOPK k j l hdr)) := by
      unfold pqxdhKeyIndImpl; dsimp only; prove_preserves_at
    exact fun x hx => h_from_proj x.2 (hp x hx)
  | testSession sid =>
    let projTest := fun s : KeyIndState S =>
      (s.principals, s.spkBundles, s.opkEntries, sessPksKeyInd S s)
    have h_step : ∀ (s : KeyIndState S),
        projTest { s with sessions := s.sessions.map (fun e =>
          if e.sid == sid then { e with tested := true } else e) } = projTest s := by
      intro s
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
      dsimp only [projTest, sessPksKeyInd]
      rw [List.map_map]
      refine List.map_congr_left (fun e _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projTest st (pqxdhKeyIndImpl useRo S P (.testSession sid)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _)
        | (split; try dsimp only))
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : sessPksKeyInd S x.2 = sessPksKeyInd S st :=
        congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    exact ⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hVSess⟩
  | revealSessionKey sid =>
    let projTest := fun s : KeyIndState S =>
      (s.principals, s.spkBundles, s.opkEntries, sessPksKeyInd S s)
    have h_step : ∀ (s : KeyIndState S),
        projTest { s with sessions := s.sessions.map (fun e =>
          if e.sid == sid then { e with revealed := true } else e) } = projTest s := by
      intro s
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
      dsimp only [projTest, sessPksKeyInd]
      rw [List.map_map]
      refine List.map_congr_left (fun e _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projTest st (pqxdhKeyIndImpl useRo S P (.revealSessionKey sid)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _)
        | (split; try dsimp only))
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : sessPksKeyInd S x.2 = sessPksKeyInd S st :=
        congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    exact ⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hVSess⟩
  | roQuery secrets =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.roQuery secrets)) := by
      unfold pqxdhKeyIndImpl; dsimp only; prove_preserves_at
    exact fun x hx => h_from_proj x.2 (hp x hx)
  | revealDhSecrets =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P .revealDhSecrets) := by
      unfold pqxdhKeyIndImpl; dsimp only; prove_preserves_at
    exact fun x hx => h_from_proj x.2 (hp x hx)
  | registerKey sk =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.registerKey sk)) := by
      unfold pqxdhKeyIndImpl registerAdvKey; dsimp only; prove_preserves_at
    exact fun x hx => h_from_proj x.2 (hp x hx)
  | revealSpkSk u j =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      simp [StateT.run_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      have h_rev := validSpkBundles_map_revealed S P (u.val, j.val) st.spkBundles hVS
      intro x hx
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨hVP, h_rev.1, hVO, hVSess⟩


end SignalPqxdh.Security
