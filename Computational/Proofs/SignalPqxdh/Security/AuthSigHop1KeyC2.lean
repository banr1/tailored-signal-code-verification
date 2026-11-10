/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyC0

/-!
# One-key `Auth` bad-signature hop: signing-log lemmas for the `GapSigEufCma` simulator

**Checked by Lean.** Shows that `gapSigEufCmaFullImpl` threads its signing log additively, projects
to `gapDhWithSignFullImpl` when forgetting the log, and under `fgAuth1KeyStepHalt` logs only the
target principal's newly signed pre-keys.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

theorem gapSigEufCmaFullImpl_run_append_query (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (q : (ℕ ⊕ PrimQuery) ⊕ (SigQuery ⊕ DdhQuery))
    (l : List Bytes) :
    (gapSigEufCmaFullImpl P ddh sk q).run l =
      (fun x => (x.1, x.2 ++ l)) <$> (gapSigEufCmaFullImpl P ddh sk q).run [] := by
  rcases q with bq | (⟨m⟩ | dq)
  · simp [gapSigEufCmaFullImpl, QueryImpl.liftTarget, StateT.run_monadLift]
  · simp [gapSigEufCmaFullImpl, gapSigEufCmaSigImpl, StateT.run_bind, StateT.run_monadLift,
      StateT.run_modify]
  · simp [gapSigEufCmaFullImpl, gapSigEufCmaDdhImpl]

theorem simulateQ_gapSigEufCmaFullImpl_run_append {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (oa : OracleComp SigDdhSimSpec α)
    (l : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) oa).run l =
      (fun x => (x.1, x.2 ++ l)) <$> (simulateQ (gapSigEufCmaFullImpl P ddh sk) oa).run [] := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [gapSigEufCmaFullImpl_run_append_query P ddh sk q l, bind_map_left, map_bind]
    congr 1; funext x
    rw [ih _ (x.2 ++ l), ih _ x.2]
    simp [Functor.map_map, List.append_assoc]

theorem fst_gapSigEufCmaFullImpl_run_query (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (q : (ℕ ⊕ PrimQuery) ⊕ (SigQuery ⊕ DdhQuery))
    (l : List Bytes) :
    Prod.fst <$> (gapSigEufCmaFullImpl P ddh sk q).run l = gapDhWithSignFullImpl P sk ddh q := by
  rcases q with bq | (⟨m⟩ | dq)
  · simp [gapSigEufCmaFullImpl, gapDhWithSignFullImpl, QueryImpl.liftTarget,
      StateT.run_monadLift]
  · simp [gapSigEufCmaFullImpl, gapSigEufCmaSigImpl, gapDhWithSignFullImpl, gapDhSigImpl,
      StateT.run_bind, StateT.run_monadLift, StateT.run_modify]
  · simp [gapSigEufCmaFullImpl, gapSigEufCmaDdhImpl, gapDhWithSignFullImpl]
    rfl

theorem fst_simulateQ_gapSigEufCmaFullImpl_run {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (oa : OracleComp SigDdhSimSpec α)
    (l : List Bytes) :
    Prod.fst <$> (simulateQ (gapSigEufCmaFullImpl P ddh sk) oa).run l =
      simulateQ (gapDhWithSignFullImpl P sk ddh) oa := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rw [← fst_gapSigEufCmaFullImpl_run_query P ddh sk q l, bind_map_left]
    congr 1; funext x
    exact ih _ x.2

theorem simulateQ_gapSigEufCmaFullImpl_liftGdhToSign_run {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (mx : OracleComp GdhSimSpec α)
    (l : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (liftGdhToSign mx)).run l =
      (fun a => (a, l)) <$> simulateQ (gapDhFullImpl P ddh) mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    cases q with
    | inl bq =>
      change (simulateQ (gapSigEufCmaFullImpl P ddh sk)
          (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
            fun u => liftGdhToSign (k u))).run l =
        (fun a => (a, l)) <$> simulateQ (gapDhFullImpl P ddh)
          (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl bq)) >>= k)
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      simp [gapSigEufCmaFullImpl, gapDhFullImpl, QueryImpl.liftTarget, StateT.run_monadLift]
      refine bind_congr (fun a => ?_)
      exact ih a
    | inr dq =>
      change (simulateQ (gapSigEufCmaFullImpl P ddh sk)
          (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
            fun u => liftGdhToSign (k u))).run l =
        (fun a => (a, l)) <$> simulateQ (gapDhFullImpl P ddh)
          (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inr dq)) >>= k)
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      simp [gapSigEufCmaFullImpl, gapSigEufCmaDdhImpl, gapDhFullImpl, gapDhDdhImpl]
      exact ih _


@[simp]
theorem simulateQ_gapSigEufCmaFullImpl_primGdhSignQ_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (op : PrimQuery) (l : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (primGdhSignQ op)).run l =
      (fun a => (a, l)) <$> primImpl P op := by
  unfold primGdhSignQ gapSigEufCmaFullImpl
  simp [QueryImpl.liftTarget, primBaseImpl, StateT.run_monadLift]

@[simp]
theorem simulateQ_gapSigEufCmaFullImpl_primGdhSignQ_x25519Base_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk s : Bytes) (l : List Bytes) :
    (simulateQ (α := Bytes) (gapSigEufCmaFullImpl P ddh sk) (primGdhSignQ (.x25519Base s))).run l =
      pure (P.x25519Base s, l) := by
  rw [simulateQ_gapSigEufCmaFullImpl_primGdhSignQ_run]; rfl

@[simp]
theorem simulateQ_gapSigEufCmaFullImpl_primGdhSignQ_kemKeyGen_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk seed : Bytes) (l : List Bytes) :
    (simulateQ (α := Bytes × Bytes) (gapSigEufCmaFullImpl P ddh sk)
      (primGdhSignQ (.kemKeyGen seed))).run l = pure (P.kemKeyGen seed, l) := by
  rw [simulateQ_gapSigEufCmaFullImpl_primGdhSignQ_run]; rfl

@[simp]
theorem simulateQ_gapSigEufCmaFullImpl_sigChalQGdh_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (msg : Bytes) (l : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (FgGapDh1Key.sigChalQ msg)).run l =
      (fun r => (P.sigSign sk msg r, msg :: l)) <$> sampleRandom64 := by
  unfold FgGapDh1Key.sigChalQ gapSigEufCmaFullImpl gapSigEufCmaSigImpl
  simp [StateT.run_bind, StateT.run_monadLift, StateT.run_modify, map_eq_bind_pure_comp]

@[simp]
theorem simulateQ_gapSigEufCmaFullImpl_unifGdhSign_run {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (mx : ProbComp α) (l : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (unifGdhSign mx)).run l =
      (fun a => (a, l)) <$> mx := by
  rw [unifGdhSign_eq_unifSigDdh, simulateQ_unifSigDdh_run]

theorem log_nil_of_mem_support_liftAuthSimStep1Key {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (f : FgAuthSimState S → OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S))
    (st : FgAuth1KeySimState S) :
    ∀ x ∈ support ((simulateQ (gapSigEufCmaFullImpl P ddh sk) (liftAuthSimStep1Key f st)).run []),
      x.2 = [] := by
  intro x hx
  unfold liftAuthSimStep1Key at hx
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_gapSigEufCmaFullImpl_liftGdhToSign_run,
    bind_map_left, simulateQ_pure, StateT.run_pure, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hx
  rcases hx with ⟨_, _, rfl⟩
  rfl

theorem log_nil_of_mem_support_fgAuthInitPrin1KeyGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (prinFlag : Bool) (prinIdx : ℕ)
    (Up : Bytes) (u : Fin S.N_id) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support ((simulateQ (gapSigEufCmaFullImpl P ddh sk)
        (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st)).run []),
      x.2 = [] := by
  intro x hx
  unfold fgAuthInitPrin1KeyGdh at hx
  by_cases hAny : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
  · simp only [hAny, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hx
    subst hx; rfl
  · simp [hAny, simulateQ_bind, StateT.run_bind] at hx
    rcases hx with ⟨_, _, rfl⟩
    rfl

theorem log_subset_of_mem_support_fgAuthGenSPK1KeyGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (k targetIdx targetSpkIdx : ℕ) (S : Setup)
    (maxLen : ℕ) (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support ((simulateQ (gapSigEufCmaFullImpl P ddh sk)
        (fgAuthGenSPK1KeyGdh true k true targetIdx targetSpkIdx S maxLen U V u j st)).run []),
      ∀ m ∈ x.2, m ∈ bundleSignedMessages k x.1.2.sim.base.spkBundles := by
  intro x hx m hm
  unfold fgAuthGenSPK1KeyGdh at hx
  by_cases hu : (u.val == k) = true
  · have huk : u.val = k := beq_iff_eq.mp hu
    by_cases hAny : st.sim.base.spkBundles.any (fun (kk, _) => kk == (u.val, j.val)) = true
    · simp [hu, hAny] at hx; subst hx; simp at hm
    · cases hF : st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [hu, hAny, hF] at hx; subst hx; simp at hm
      | some p =>
        by_cases hB : st.sigBudget = 0
        · simp [hu, hAny, hF, hB] at hx; subst hx; simp at hm
        · simp [hu, hAny, hF, hB, simulateQ_bind, StateT.run_bind] at hx
          rcases hx with ⟨_, _, _, _, _, _, _, _, rfl⟩
          subst huk
          simp only [bundleSignedMessages_cons_eq, List.mem_cons,
            List.not_mem_nil, or_false] at hm ⊢
          rcases hm with rfl | rfl <;> simp
  · simp only [hu, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hx
    rw [log_nil_of_mem_support_liftAuthSimStep1Key P ddh sk _ st x hx] at hm
    simp at hm


theorem log_subset_of_mem_support_fgAuth1KeyStepHalt (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) (k targetSpkIdx : ℕ) (S : Setup)
    (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support ((simulateQ (gapSigEufCmaFullImpl P ddh sk)
        (fgAuth1KeyStepHalt true k targetSpkIdx S maxLen U V q st)).run []),
      ∀ m ∈ x.2, m ∈ bundleSignedMessages k x.1.2.sim.base.spkBundles := by
  intro x hx m hm
  unfold fgAuth1KeyStepHalt at hx
  by_cases hc : (true && isTargetPrinCorrupted k st.sim) = true
  · simp only [hc, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hx
    subst hx; simp at hm
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hx
    have hnil : ∀ (f : FgAuthSimState S → OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S)),
        x ∈ support ((simulateQ (gapSigEufCmaFullImpl P ddh sk)
          (liftAuthSimStep1Key f st)).run []) → False := by
      intro f hxf
      rw [log_nil_of_mem_support_liftAuthSimStep1Key P ddh sk f st x hxf] at hm
      simp at hm
    cases q with
    | initPrin u =>
      rw [log_nil_of_mem_support_fgAuthInitPrin1KeyGdh P ddh sk true k U u st x hx] at hm
      simp at hm
    | genSPK u j =>
      exact log_subset_of_mem_support_fgAuthGenSPK1KeyGdh P ddh sk k k targetSpkIdx S maxLen U V
        u j st x hx m hm
    | _ => exact (hnil _ hx).elim

end Proofs.SignalPqxdh.Security
