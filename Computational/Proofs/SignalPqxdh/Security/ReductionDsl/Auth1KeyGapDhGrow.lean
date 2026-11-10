/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhGrow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhEvalEq
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Step Growth of the One-Key `Auth` Gap-DH Simulator

**Checked by Lean.** Proves that one step of `fgAuth1KeyStepHalt` grows each tracked list by at
most one entry, preserving the length and signing-budget invariants `AgInv` and `AgInv2`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open SignalPqxdh SignalPqxdh.Security
open SignalPqxdh.Security.FgGapDh1Key Proofs.SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open OracleSpec OracleComp

theorem liftAuthSimStep1Key_grow {S : Setup}
    (f : FgAuthSimState S → OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S))
    (st : FgAuth1KeySimState S)
    (hf : ∀ y ∈ support (f st.sim), AGrow st.sim y.2) :
    ∀ x ∈ support (liftAuthSimStep1Key f st), AGrow st.sim x.2.sim := by
  intro x hx
  unfold liftAuthSimStep1Key at hx
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨resp, sim'⟩, hy, rfl⟩
  exact hf (resp, sim') (mem_support_liftGdhToSign hy)

theorem fgAuthInitPrin1KeyGdh_grow {S : Setup} (prinFlag : Bool) (prinIdx : Nat) (Up : Bytes)
    (u : Fin S.N_id) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st), AGrow st.sim x.2.sim := by
  show AllOut (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st) (fun x => AGrow st.sim x.2.sim)
  unfold fgAuthInitPrin1KeyGdh
  agrow_loop
  all_goals agrow_leaf

theorem fgAuthGenSPK1KeyGdh_grow {S : Setup} (prinFlag : Bool) (prinIdx : Nat)
    (useDh1 : Bool) (targetIdx targetSpkIdx K : Nat) (U V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support
        (fgAuthGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S K U V u j st),
      AGrow st.sim x.2.sim := by
  unfold fgAuthGenSPK1KeyGdh
  by_cases hT : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hT, ↓reduceIte]
    show AllOut _ (fun (x : AuthResponse × FgAuth1KeySimState S) => AGrow st.sim x.2.sim)
    agrow_loop
    all_goals agrow_leaf
  · simp only [hT, Bool.false_eq_true, ↓reduceIte]
    exact liftAuthSimStep1Key_grow _ st
      (fgAuthStep_grow useDh1 targetIdx targetSpkIdx K U V (.genSPK u j) st.sim)

theorem fgAuth1KeyStep_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support (fgAuth1KeyStep useDh1 t s S K U V q st), AGrow st.sim x.2.sim := by
  unfold fgAuth1KeyStep
  split
  · exact fgAuthInitPrin1KeyGdh_grow useDh1 t U _ st
  · exact fgAuthGenSPK1KeyGdh_grow useDh1 t useDh1 t s K U V _ _ st
  · exact liftAuthSimStep1Key_grow _ st (fgAuthStep_grow useDh1 t s K U V _ st.sim)

theorem fgAuth1KeyStepHalt_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support (fgAuth1KeyStepHalt useDh1 t s S K U V q st), AGrow st.sim x.2.sim := by
  unfold fgAuth1KeyStepHalt
  split
  · exact AllOut.pure_of (by agrow_leaf)
  · exact fgAuth1KeyStep_grow _ _ _ _ _ _ _ _

theorem fgAuth1KeyStepHalt_agInv {S : Setup} (useDh1 : Bool) (t s K k : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuth1KeySimState S) (h : AgInv K (k + 1) st.sim) :
    ∀ x ∈ support (fgAuth1KeyStepHalt useDh1 t s S K U V q st), AgInv K k x.2.sim :=
  fun x hx => AgInv.of_grow K k st.sim x.2.sim h (fgAuth1KeyStepHalt_grow _ _ _ _ _ _ _ _ x hx)

private theorem liftAuthSimStep1Key_respRecs_grow {S : Setup}
    (f : FgAuthSimState S → OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S))
    (st : FgAuth1KeySimState S)
    (hf : ∀ y ∈ support (f st.sim), y.2.respRecs.length ≤ st.sim.respRecs.length + 1) :
    ∀ x ∈ support (liftAuthSimStep1Key f st),
      x.2.sim.respRecs.length ≤ st.sim.respRecs.length + 1 := by
  intro x hx
  unfold liftAuthSimStep1Key at hx
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨resp, sim'⟩, hy, rfl⟩
  exact hf (resp, sim') (mem_support_liftGdhToSign hy)

private theorem fgAuthInitPrin1KeyGdh_respRecs_grow {S : Setup} (prinFlag : Bool) (prinIdx : Nat)
    (Up : Bytes) (u : Fin S.N_id) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st),
      x.2.sim.respRecs.length ≤ st.sim.respRecs.length + 1 := by
  show AllOut (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st)
    (fun x => x.2.sim.respRecs.length ≤ st.sim.respRecs.length + 1)
  unfold fgAuthInitPrin1KeyGdh
  agrow_loop
  all_goals exact Nat.le_succ _

private theorem fgAuthGenSPK1KeyGdh_respRecs_grow {S : Setup} (prinFlag : Bool) (prinIdx : Nat)
    (useDh1 : Bool) (targetIdx targetSpkIdx K : Nat) (U V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support
        (fgAuthGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S K U V u j st),
      x.2.sim.respRecs.length ≤ st.sim.respRecs.length + 1 := by
  unfold fgAuthGenSPK1KeyGdh
  by_cases hT : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hT, ↓reduceIte]
    show AllOut _ (fun (x : AuthResponse × FgAuth1KeySimState S) =>
      x.2.sim.respRecs.length ≤ st.sim.respRecs.length + 1)
    agrow_loop
    all_goals exact Nat.le_succ _
  · simp only [hT, Bool.false_eq_true, ↓reduceIte]
    exact liftAuthSimStep1Key_respRecs_grow _ st
      (fgAuthStep_respRecs_grow useDh1 targetIdx targetSpkIdx K U V (.genSPK u j) st.sim)

theorem fgAuth1KeyStepHalt_respRecs_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support (fgAuth1KeyStepHalt useDh1 t s S K U V q st),
      x.2.sim.respRecs.length ≤ st.sim.respRecs.length + 1 := by
  unfold fgAuth1KeyStepHalt
  split
  · exact AllOut.pure_of (Nat.le_succ _)
  · unfold fgAuth1KeyStep
    split
    · exact fgAuthInitPrin1KeyGdh_respRecs_grow useDh1 t U _ st
    · exact fgAuthGenSPK1KeyGdh_respRecs_grow useDh1 t useDh1 t s K U V _ _ st
    · exact liftAuthSimStep1Key_respRecs_grow _ st (fgAuthStep_respRecs_grow useDh1 t s K U V _ st.sim)

private theorem fgAuth1KeyStepHalt_sigBudget_step {S : Setup} (useDh1 : Bool) (t s K : Nat)
    (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    ∀ x ∈ support (fgAuth1KeyStepHalt useDh1 t s S K U V q st),
      st.sigBudget ≤ x.2.sigBudget + 1 ∧ x.2.sigBudget ≤ st.sigBudget := by
  show AllOut (fgAuth1KeyStepHalt useDh1 t s S K U V q st)
    (fun x => st.sigBudget ≤ x.2.sigBudget + 1 ∧ x.2.sigBudget ≤ st.sigBudget)
  unfold fgAuth1KeyStepHalt
  split
  · exact AllOut.pure_of (by dsimp only; omega)
  · unfold fgAuth1KeyStep
    split
    · unfold fgAuthInitPrin1KeyGdh
      agrow_loop
      all_goals omega
    · rename_i u j
      unfold fgAuthGenSPK1KeyGdh
      by_cases hT : (useDh1 && (u.val == t)) = true
      · simp only [hT, ↓reduceIte]
        agrow_loop
        all_goals omega
      · simp only [hT, Bool.false_eq_true, ↓reduceIte]
        unfold liftAuthSimStep1Key
        agrow_loop
        all_goals omega
    · unfold liftAuthSimStep1Key
      agrow_loop
      all_goals omega

/-- Length and signing-budget invariant for the tuple-keyed `a1g2` simulator. -/
def AgInv2 {S : Setup} (K k : Nat) (st : FgAuth1KeySimState S) : Prop :=
  AgInv K k st.sim ∧
  k + st.sim.respRecs.length ≤ K ∧
  st.sigBudget ≤ min S.N_spk_tot S.N_recv ∧
  k + (min S.N_spk_tot S.N_recv - st.sigBudget) ≤ K

theorem AgInv2.mono {S : Setup} (K k : Nat) (st : FgAuth1KeySimState S)
    (h : AgInv2 K (k + 1) st) : AgInv2 K k st := by
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨AgInv.mono K k st.sim h1, by omega, h3, by omega⟩

theorem AgInv2.empty (S : Setup) (K : Nat) (secb : Bool) :
    AgInv2 K K (FgAuth1KeySimState.empty S secb) := by
  refine ⟨AgInv.empty S K secb, ?_, ?_, ?_⟩ <;>
    simp [FgAuth1KeySimState.empty, FgAuthSimState.empty]

theorem AgInv2.bnd {S : Setup} (K k : Nat) (st : FgAuth1KeySimState S) (h : AgInv2 K k st) :
    AgBnd K st.sim :=
  AgInv.bnd K k st.sim h.1

theorem fgAuth1KeyStepHalt_agInv2 {S : Setup} (useDh1 : Bool) (t s K k : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuth1KeySimState S) (h : AgInv2 K (k + 1) st) :
    ∀ x ∈ support (fgAuth1KeyStepHalt useDh1 t s S K U V q st), AgInv2 K k x.2 := by
  intro x hx
  have h1 := fgAuth1KeyStepHalt_agInv useDh1 t s K k U V q st h.1 x hx
  have h2 := fgAuth1KeyStepHalt_respRecs_grow useDh1 t s K U V q st x hx
  have h3 := fgAuth1KeyStepHalt_sigBudget_step useDh1 t s K U V q st x hx
  refine ⟨h1, ?_, ?_, ?_⟩
  · have := h.2.1; omega
  · have := h.2.2.1; omega
  · have := h.2.2.1; have := h.2.2.2; omega

end SignalPqxdh.Security.ReductionDsl.AuthHs
