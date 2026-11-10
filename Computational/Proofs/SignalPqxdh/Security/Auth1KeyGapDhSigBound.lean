/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyPre

/-!
# Signing-query bound for the one-key `Auth` `GapDhWithSign` reduction

**Checked by Lean.** Proves that `fgAuth1KeyGapDhAdv4 S b A` issues at most
`2 * min S.N_spk_tot S.N_recv` challenger `.sign` queries by tracking `st.sigBudget` across
per-query steps.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

private theorem a1sigQb_pure {α : Type} (a : α) :
    IsQueryBoundP (pure a : OracleComp GdhSignSimSpec α) (fun q => isSigChalQuery q = true) 0 :=
  isQueryBoundP_pure _ a 0

private theorem a1sigQb_bind0 {α β : Type} {mx : OracleComp GdhSignSimSpec α}
    {k : α → OracleComp GdhSignSimSpec β} {n : ℕ}
    (h1 : IsQueryBoundP mx (fun q => isSigChalQuery q = true) 0)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (k x) (fun q => isSigChalQuery q = true) n) :
    IsQueryBoundP (mx >>= k) (fun q => isSigChalQuery q = true) n := by
  simpa using isQueryBoundP_bind h1 h2

private theorem a1sigQb_bind1 {α β : Type} {mx : OracleComp GdhSignSimSpec α}
    {k : α → OracleComp GdhSignSimSpec β} {n : ℕ}
    (h1 : IsQueryBoundP mx (fun q => isSigChalQuery q = true) 1)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (k x) (fun q => isSigChalQuery q = true) n) :
    IsQueryBoundP (mx >>= k) (fun q => isSigChalQuery q = true) (1 + n) :=
  isQueryBoundP_bind h1 h2

/-- Step-level signing-budget accounting invariant for `FgAuth1KeySimState`. -/
def AuthSigBudgetStepInv {S : Setup} {R : Type}
    (m : OracleComp GdhSignSimSpec (R × FgAuth1KeySimState S)) (b : ℕ) : Prop :=
  ∃ k ≤ b,
    IsQueryBoundP m (fun q => isSigChalQuery q = true) (2 * k) ∧
    ∀ x ∈ support m, x.2.sigBudget ≤ b - k

theorem authSigBudgetStepInv_liftAuthSimStep1Key {S : Setup}
    (f : FgAuthSimState S → OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S))
    (st : FgAuth1KeySimState S) :
    AuthSigBudgetStepInv (liftAuthSimStep1Key f st) st.sigBudget := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · unfold liftAuthSimStep1Key
    exact (isQueryBoundP_bind (isQueryBoundP_liftGdhToSign_sig (f st.sim) 0)
      (fun _ _ => a1sigQb_pure _)).mono (by omega)
  · intro x hx
    unfold liftAuthSimStep1Key at hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨_, _⟩, _, rfl⟩
    dsimp only; omega

theorem authSigBudgetStepInv_fgAuthInitPrin1KeyGdh {S : Setup}
    (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes) (u : Fin S.N_id)
    (st : FgAuth1KeySimState S) :
    AuthSigBudgetStepInv (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st) st.sigBudget := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · unfold fgAuthInitPrin1KeyGdh
    by_cases hAny : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hAny, ↓reduceIte]
      exact a1sigQb_pure _
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      refine a1sigQb_bind0 (isQueryBoundP_unifGdhSign_sig sampleScalar32 0) (fun sk0 _ => ?_)
      exact a1sigQb_bind0 (isQueryBoundP_primGdhSignQ_sig (.x25519Base sk0) 0)
        (fun _ _ => a1sigQb_pure _)
  · intro x hx
    unfold fgAuthInitPrin1KeyGdh at hx
    by_cases hAny : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp [hAny] at hx; subst hx; dsimp only; omega
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨_, _, _, _, rfl⟩
      dsimp only; omega

theorem authSigBudgetStepInv_fgAuthGenSPK1KeyGdh (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgAuth1KeySimState S) :
    AuthSigBudgetStepInv
      (fgAuthGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st)
      st.sigBudget := by
  unfold fgAuthGenSPK1KeyGdh
  by_cases hPrin : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hPrin, ↓reduceIte]
    by_cases hAny : (st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · simp only [hAny, ↓reduceIte]; exact a1sigQb_pure _
      · intro x hx; simp [hAny] at hx; subst hx; dsimp only; omega
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      cases hFind : st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        refine ⟨0, Nat.zero_le _, a1sigQb_pure _, ?_⟩
        intro x hx; simp at hx; subst hx; dsimp only; omega
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        by_cases hZero : (st.sigBudget == 0) = true
        · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
          · simp only [hZero, ↓reduceIte]; exact a1sigQb_pure _
          · intro x hx; simp [hZero] at hx; subst hx; dsimp only; omega
        · have hPos : 1 ≤ st.sigBudget := by
            have hNe : st.sigBudget ≠ 0 := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hZero)
            omega
          simp only [hZero, Bool.false_eq_true, ↓reduceIte]
          refine ⟨1, hPos, ?_, ?_⟩
          · refine a1sigQb_bind0 (isQueryBoundP_unifGdhSign_sig sampleScalar32 0)
              (fun spkSkRaw _ => ?_)
            refine a1sigQb_bind0 (isQueryBoundP_primGdhSignQ_sig (.x25519Base spkSkRaw) 0)
              (fun spkPkRaw _ => ?_)
            change IsQueryBoundP _ _ (1 + (1 + 0))
            refine a1sigQb_bind1 (isQueryBoundP_sigChalQ_sig _) (fun _ _ => ?_)
            refine a1sigQb_bind0 (isQueryBoundP_unifGdhSign_sig sampleRandom64 0)
              (fun seedKem _ => ?_)
            refine a1sigQb_bind0 (isQueryBoundP_primGdhSignQ_sig (.kemKeyGen seedKem) 0)
              (fun pqPair _ => ?_)
            exact a1sigQb_bind1 (isQueryBoundP_sigChalQ_sig _) (fun _ _ => a1sigQb_pure _)
          · intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨_, _, _, _, _, _, _, _, ⟨_, _⟩, _, _, _, rfl⟩
            dsimp only; omega
  · simp only [hPrin, Bool.false_eq_true, ↓reduceIte]
    exact authSigBudgetStepInv_liftAuthSimStep1Key _ st

theorem authSigBudgetStepInv_fgAuth1KeyStep (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    AuthSigBudgetStepInv (fgAuth1KeyStep useDh1 targetIdx targetSpkIdx S maxLen U V q st)
      st.sigBudget := by
  cases q with
  | initPrin u => exact authSigBudgetStepInv_fgAuthInitPrin1KeyGdh useDh1 targetIdx U u st
  | genSPK u j =>
    exact authSigBudgetStepInv_fgAuthGenSPK1KeyGdh useDh1 targetIdx useDh1 targetIdx
      targetSpkIdx S maxLen U V u j st
  | _ => exact authSigBudgetStepInv_liftAuthSimStep1Key _ st

theorem authSigBudgetStepInv_fgAuth1KeyStepHalt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    AuthSigBudgetStepInv (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V q st)
      st.sigBudget := by
  unfold fgAuth1KeyStepHalt
  split_ifs
  · refine ⟨0, Nat.zero_le _, a1sigQb_pure _, ?_⟩
    intro x hx; simp at hx; subst hx; dsimp only; omega
  · exact authSigBudgetStepInv_fgAuth1KeyStep useDh1 targetIdx targetSpkIdx S maxLen U V q st

theorem isQueryBoundP_runWithGdhSignStep_auth1Key_sig {S : Setup} {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {α : Type}
    (step : (q : ιI) → FgAuth1KeySimState S →
      OracleComp GdhSignSimSpec (GSpec.Range q × FgAuth1KeySimState S))
    (h_step : ∀ gq st, AuthSigBudgetStepInv (step gq st) st.sigBudget)
    (mx : OracleComp (unifSpec + GSpec) α) (st : FgAuth1KeySimState S) :
    IsQueryBoundP (runWithGdhSignStep step mx st)
      (fun q => isSigChalQuery q = true) (2 * st.sigBudget) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => simp [runWithGdhSignStep_pure]
  | query_bind q r ih =>
    cases q with
    | inl n =>
      rw [runWithGdhSignStep_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u => ih u st⟩
    | inr gq =>
      rw [runWithGdhSignStep_query_inr]
      rcases h_step gq st with ⟨k, hkLe, hQbStep, hSup⟩
      have hCont : ∀ p ∈ support (step gq st),
          IsQueryBoundP (runWithGdhSignStep step (r p.1) p.2)
            (fun q => isSigChalQuery q = true) (2 * (st.sigBudget - k)) :=
        fun p hp => (ih p.1 p.2).mono (by have := hSup p hp; omega)
      exact (isQueryBoundP_bind hQbStep hCont).mono (by omega)

theorem isQueryBoundP_fgAuth1KeyGapDhRunAt_sig (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    IsQueryBoundP (fgAuth1KeyGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V)
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  unfold fgAuth1KeyGapDhRunAt
  refine a1sigQb_bind0 (isQueryBoundP_unifGdhSign_sig ($ᵗ Bool) 0) (fun secb _ => ?_)
  have hStep : IsQueryBoundP
      (runWithGdhSignStep (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S b.q_total U V)
        A.1.run (FgAuth1KeySimState.empty S secb))
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) :=
    isQueryBoundP_runWithGdhSignStep_auth1Key_sig _
      (authSigBudgetStepInv_fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S b.q_total U V)
      A.1.run (FgAuth1KeySimState.empty S secb)
  exact (isQueryBoundP_bind hStep
    (fun p _ => isQueryBoundP_liftGdhToSign_sig _ 0)).mono (by omega)

/-- Semantic signing-query bound for `fgAuth1KeyGapDhAdv4`. -/
theorem isQueryBoundP_fgAuth1KeyGapDhAdv4_sig
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    IsQueryBoundP ((fgAuth1KeyGapDhAdv4 S b A).run U V)
      (fun q => isSigChalQuery q = true) (fgAuth1KeyGapDhAdv4 S b A).q_sig := by
  dsimp only [fgAuth1KeyGapDhAdv4]
  refine a1sigQb_bind0
    (isQueryBoundP_unifGdhSign_sig (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) 0)
    (fun p _ => ?_)
  rcases p with ⟨fl, bI⟩
  dsimp only
  split_ifs
  · exact isQueryBoundP_fgAuth1KeyGapDhRunAt_sig _ _ _ S b A U V
  · exact isQueryBoundP_fgAuth1KeyGapDhRunAt_sig _ _ _ S b A U V

end Proofs.SignalPqxdh.Security
