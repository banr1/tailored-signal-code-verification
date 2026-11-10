/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhSigBound
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuth1KeySig

/-!
# Signing-query bound for the one-key `Auth` `GapSigEufCma` reduction

**Checked by Lean.** Proves that `(sigReductionAuth1Key S b A).run pk` issues at most
`2 * min S.N_spk_tot S.N_recv` challenger `.sign` queries via
`authSigBudgetStepInv_fgAuth1KeyStepHalt`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

theorem isQueryBoundP_embedPrim_sigChal {α : Type} (mx : OracleComp PrimBaseSpec α) (n : ℕ) :
    IsQueryBoundP (SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) mx)
      (fun q => isSigChalQuery q = true) n := by
  induction mx using OracleComp.inductionOn generalizing n with
  | pure a => exact (isQueryBoundP_pure _ a 0).mono (Nat.zero_le n)
  | query_bind q k ih =>
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (Sum.inl q)) >>=
        fun u => SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) (k u))
      (fun q => isSigChalQuery q = true) n
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (fun h => by cases h), fun u => ih u n⟩

theorem isQueryBoundP_bind_le_of {α β : Type} {mx : OracleComp GdhSignSimSpec α}
    {k : α → OracleComp GdhSignSimSpec β} {n : ℕ}
    (h1 : IsQueryBoundP mx (fun q => isSigChalQuery q = true) 0)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (k x) (fun q => isSigChalQuery q = true) n) :
    IsQueryBoundP (mx >>= k) (fun q => isSigChalQuery q = true) n := by
  simpa using isQueryBoundP_bind h1 h2

/-- Continuation-style signing-budget invariant for a step over `SigAuth1KeySimState`. -/
def SigAuth1KeySigPot {S : Setup} {R : Type}
    (m : OracleComp GdhSignSimSpec (R × SigAuth1KeySimState S)) (b : ℕ) : Prop :=
  ∀ {β : Type} (k : R × SigAuth1KeySimState S → OracleComp GdhSignSimSpec β),
    (∀ p, IsQueryBoundP (k p) (fun q => isSigChalQuery q = true) (2 * p.2.fg.sigBudget)) →
    IsQueryBoundP (m >>= k) (fun q => isSigChalQuery q = true) (2 * b)

theorem sigAuth1KeySigPot_pure {S : Setup} {R : Type} (r : R) (st : SigAuth1KeySimState S) :
    SigAuth1KeySigPot (pure (r, st) : OracleComp GdhSignSimSpec _) st.fg.sigBudget := by
  intro β k hk
  simpa using hk (r, st)

theorem sigAuth1KeySigPot_delegate (S : Setup) (maxLen : ℕ) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) :
    SigAuth1KeySigPot (sigAuth1KeyDelegate S maxLen q st) st.fg.sigBudget := by
  intro β k hk
  unfold sigAuth1KeyDelegate
  rw [bind_assoc]
  rcases authSigBudgetStepInv_fgAuth1KeyStepHalt true st.targetParty S.N_spk_tot S maxLen
    st.targetPk st.targetPk q st.fg with ⟨j, hjLe, hQb, hSup⟩
  have hC : ∀ p ∈ support (fgAuth1KeyStepHalt true st.targetParty S.N_spk_tot S maxLen
      st.targetPk st.targetPk q st.fg),
      IsQueryBoundP ((fun x => pure (x.1, { st with fg := x.2 }) >>= k) p)
        (fun q => isSigChalQuery q = true) (2 * (st.fg.sigBudget - j)) := by
    rintro ⟨out, fg'⟩ hp
    simp only [pure_bind]
    exact (hk (out, { st with fg := fg' })).mono (by have := hSup _ hp; dsimp only at this ⊢; omega)
  have h := isQueryBoundP_bind hQb hC
  exact h.mono (by omega)

theorem sigAuth1KeySigPot_send (S : Setup) (maxLen : ℕ) (q : AuthQuery S)
    (bundle : PreKeyBundleInput) (st : SigAuth1KeySimState S) :
    SigAuth1KeySigPot (sigAuth1KeySend S maxLen q bundle st) st.fg.sigBudget := by
  intro β k hk
  unfold sigAuth1KeySend
  rw [bind_assoc]
  refine isQueryBoundP_bind_le_of (isQueryBoundP_embedPrim_sigChal _ 0) ?_
  intro f' _
  split_ifs
  · simpa using hk (.noneResp, { st with forgery := f' })
  · exact sigAuth1KeySigPot_delegate S maxLen q st k hk

theorem sigAuth1KeySigPot_step (S : Setup) (maxLen : ℕ) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) :
    SigAuth1KeySigPot (sigAuth1KeyStep S maxLen q st) st.fg.sigBudget := by
  unfold sigAuth1KeyStep
  split_ifs
  · exact sigAuth1KeySigPot_pure _ st
  · cases q with
    | sendOPK _ _ bundle _ _ => exact sigAuth1KeySigPot_send S maxLen _ bundle st
    | sendNoOPK _ _ bundle _ _ => exact sigAuth1KeySigPot_send S maxLen _ bundle st
    | _ => exact sigAuth1KeySigPot_delegate S maxLen _ st

theorem isQueryBoundP_runWithGdhSignStep_sigAuth1Key_sig {S : Setup} {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {α : Type}
    (step : (q : ιI) → SigAuth1KeySimState S →
      OracleComp GdhSignSimSpec (GSpec.Range q × SigAuth1KeySimState S))
    (h_step : ∀ gq st, SigAuth1KeySigPot (step gq st) st.fg.sigBudget)
    (mx : OracleComp (unifSpec + GSpec) α) :
    ∀ st : SigAuth1KeySimState S,
      IsQueryBoundP (runWithGdhSignStep step mx st)
        (fun q => isSigChalQuery q = true) (2 * st.fg.sigBudget) := by
  induction mx using OracleComp.inductionOn with
  | pure a => intro st; simp [runWithGdhSignStep_pure]
  | query_bind q r ih =>
    intro st
    cases q with
    | inl n =>
      rw [runWithGdhSignStep_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u => ih u st⟩
    | inr gq =>
      rw [runWithGdhSignStep_query_inr]
      exact h_step gq st (fun p => runWithGdhSignStep step (r p.1) p.2) (fun p => ih p.1 p.2)

theorem isQueryBoundP_sigReductionAuth1KeyRunAt_sig (targetParty : ℕ) (S : Setup)
    (b : QueryBudget) (A : AuthAdversary S) (pk : Bytes) :
    IsQueryBoundP (sigReductionAuth1KeyRunAt targetParty S b A pk)
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  unfold sigReductionAuth1KeyRunAt
  refine isQueryBoundP_bind_le_of (isQueryBoundP_unifGdhSign_sig ($ᵗ Bool) 0) ?_
  intro secb _
  have hRun := isQueryBoundP_runWithGdhSignStep_sigAuth1Key_sig (sigAuth1KeyStep S b.q_total)
    (fun gq st => sigAuth1KeySigPot_step S b.q_total gq st) A.run
    (SigAuth1KeySimState.empty S secb targetParty pk)
  have h := isQueryBoundP_bind hRun
    (fun p _ => (isQueryBoundP_pure (fun q => isSigChalQuery q = true)
      (p.2.forgery.getD ([], [])) 0))
  simpa [SigAuth1KeySimState.empty, FgAuth1KeySimState.empty] using h

/-- Semantic signing-query bound for `sigReductionAuth1Key`. -/
theorem isQueryBoundP_sigReductionAuth1Key_sig (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (pk : Bytes) :
    IsQueryBoundP ((sigReductionAuth1Key S b A).run pk)
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  dsimp only [sigReductionAuth1Key]
  exact isQueryBoundP_bind_le_of (isQueryBoundP_unifGdhSign_sig _ 0)
    (fun k _ => isQueryBoundP_sigReductionAuth1KeyRunAt_sig k S b A.1 pk)

end Proofs.SignalPqxdh.Security
