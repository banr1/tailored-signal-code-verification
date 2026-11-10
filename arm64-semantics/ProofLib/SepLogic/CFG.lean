/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.WP
public import ProofLib.Hoare.Safety
import Arm64.Trusted.Spec.SepLogic

/-!
# Control-Flow Graph and Loop Combinators

Step-indexed cutpoint fixpoint theorems (`SepWP.cfg_fixpoint_tree`, `SepWP.cfg_fixpoint_sep`,
`wp_idx.cfg_fixpoint`), DAG join-point combinators and tactics (`SepWP.join`, `wp_join`,
`wp_if_join`), and structured loop combinators (fuel, countdown, list-cursor, header-latch,
nested, and well-founded CPS loops with spatial frame peeling) for `SepWP`.
-/

namespace ProofLib

open Arm64

@[expose] public section

/-! ## Postcondition combinators -/

/-- Standard `SepWP` postcondition pairing a pure state predicate `R sf` with a spatial entailment
    `P_f ⊢ Q`. Reducible (`abbrev`) so `wp_done` unfolds and splits it automatically. -/
abbrev sepPost (R : State → Prop) (Q : SepProp) : State → SepProp → Prop :=
  fun sf P_f => R sf ∧ (P_f ⊢ Q)

/-- State-dependent `SepWP` postcondition pairing a pure state predicate `R sf` with a spatial
    entailment `P_f ⊢ Q sf`. -/
abbrev sepPostState (R : State → Prop) (Q : State → SepProp) : State → SepProp → Prop :=
  fun sf P_f => R sf ∧ (P_f ⊢ Q sf)

@[simp]
theorem sepPost_apply (R : State → Prop) (Q : SepProp) (sf : State) (P_f : SepProp) :
    sepPost R Q sf P_f ↔ R sf ∧ (P_f ⊢ Q) := Iff.rfl

@[simp]
theorem sepPostState_apply (R : State → Prop) (Q : State → SepProp) (sf : State) (P_f : SepProp) :
    sepPostState R Q sf P_f ↔ R sf ∧ (P_f ⊢ Q sf) := Iff.rfl

theorem sepPost_mono {R R' : State → Prop} {Q Q' : SepProp}
    (hR : ∀ s, R s → R' s) (hQ : Q ⊢ Q') :
    ∀ sf P_f, sepPost R Q sf P_f → sepPost R' Q' sf P_f := by
  intro sf P_f ⟨hr, hq⟩
  exact ⟨hR sf hr, Entails.trans hq hQ⟩

/-! ## Step-indexed cutpoint fixpoint theorems -/

/-- Step-indexed CFG transition tree from machine state `s` and spatial resource `P` at fuel `fuel`.
    Allows:
    * `.exit`: reaching `target_pc` directly with `post`,
    * `.jump`: reaching cutpoint `cut_pc l'` consuming `1 ≤ steps ≤ fuel` fuel,
    * `.jump_dyn`: reaching cutpoint `cut_pc l'` where `steps` (`1 ≤ steps ≤ fuel`) depends on the
      arrival state `s'`,
    * `.seq`: executing an intermediate `SepWP` segment to `mid_pc` before branching between exits
      and cutpoint jumps,
    * `.ite`: splitting on a conditional PC `s.pc = if c then pc1 else pc2`,
    * `.weaken_pre`: weakening the spatial precondition via `P ⊢ P'`. -/
inductive SepWP.CFGStep (prog : Program) (target_pc : BitVec 64)
    {Label : Type _} (cut_pc : Label → BitVec 64)
    (P_inv : Label → State → Nat → SepProp)
    (Inv : Label → State → Nat → Prop)
    (post : State → SepProp → Prop) (fuel : Nat)
    {oom : State → SepProp} : State → SepProp → Prop where
  | exit {s : State} {P : SepProp}
      (h : SepWP prog target_pc s P post oom) :
      SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel s P
  | jump (l' : Label) (steps : Nat) {s : State} {P : SepProp}
      (hpos : 1 ≤ steps) (hle : steps ≤ fuel)
      (h : SepWP prog (cut_pc l') s P (fun s' P' =>
        (P' ⊢ P_inv l' s' (fuel - steps)) ∧ Inv l' s' (fuel - steps)) oom) :
      SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel s P
  | jump_dyn (l' : Label) {s : State} {P : SepProp}
      (h : SepWP prog (cut_pc l') s P (fun s' P' =>
        ∃ steps : Nat, 1 ≤ steps ∧ steps ≤ fuel ∧
          (P' ⊢ P_inv l' s' (fuel - steps)) ∧ Inv l' s' (fuel - steps)) oom) :
      SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel s P
  | seq {mid_pc : BitVec 64} {s : State} {P : SepProp} {Mid : State → SepProp → Prop}
      (h1 : SepWP prog mid_pc s P Mid oom)
      (h2 : ∀ sm Pm, sm.pc = mid_pc → sm.status = .Running → Mid sm Pm →
        SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) sm Pm) :
      SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) s P
  | ite {s : State} {P : SepProp} {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
      (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
      (hthen : c → SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) (s.setPC pc1) P)
      (helse : ¬ c → SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) (s.setPC pc2) P) :
      SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) s P
  | weaken_pre {s : State} {P P' : SepProp}
      (hent : P ⊢ P')
      (h : SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) s P') :
      SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) s P

/-- Soundness of a single `SepWP.CFGStep` transition tree given the strong induction hypothesis
    at all strictly smaller fuel budgets `fuel' < fuel`. -/
theorem SepWP.CFGStep.eval {prog : Program} {target_pc : BitVec 64}
    {Label : Type _} {cut_pc : Label → BitVec 64}
    {P_inv : Label → State → Nat → SepProp}
    {Inv : Label → State → Nat → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp} {fuel : Nat} {s : State} {P : SepProp}
    (hstep : SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) s P)
    (ih : ∀ fuel', fuel' < fuel → ∀ l' s',
      s'.pc = cut_pc l' → s'.status = .Running → Inv l' s' fuel' →
      SepWP prog target_pc s' (P_inv l' s' fuel') post oom) :
    SepWP prog target_pc s P post oom := by
  induction hstep with
  | exit h =>
    exact h
  | jump l' steps hpos hle h =>
    refine SepWP.seq h ?_
    intro s' P' hpc' hrun' ⟨hent, hinv'⟩
    have hlt : fuel - steps < fuel := by omega
    exact SepWP.weaken_pre hent (ih (fuel - steps) hlt l' s' hpc' hrun' hinv')
  | jump_dyn l' h =>
    refine SepWP.seq h ?_
    intro s' P' hpc' hrun' ⟨steps, hpos, hle, hent, hinv'⟩
    have hlt : fuel - steps < fuel := by omega
    exact SepWP.weaken_pre hent (ih (fuel - steps) hlt l' s' hpc' hrun' hinv')
  | seq h1 _ ih2 =>
    refine SepWP.seq h1 ?_
    intro sm Pm hpc_m hrun_m hMid
    exact ih2 sm Pm hpc_m hrun_m hMid
  | ite hpc _ _ ihthen ihelse =>
    exact SepWP.ite hpc ihthen ihelse
  | weaken_pre hent _ ih_inner =>
    exact SepWP.weaken_pre hent ih_inner

/-- Step-indexed CFG cutpoint fixpoint theorem (transition-tree form).
    If from every cutpoint label `l`, machine state `s` at `cut_pc l`, and ranking measure `fuel`
    satisfying `Inv l s fuel`, execution can take a `SepWP.CFGStep` transition tree (either
    reaching `target_pc` with `post` or jumping to cutpoints `l'` with `fuel - steps < fuel`),
    then `Inv l0 s0 fuel` implies `SepWP prog target_pc s0 P post` for all `fuel`.
    For total-correctness `SepWP`, `fuel` is a caller-chosen well-founded `Nat` ranking
    measure over cutpoint transitions (not necessarily tied to raw machine step counts; see
    `wp_idx.cfg_fixpoint` for the machine-step-indexed partial-correctness counterpart). -/
theorem SepWP.cfg_fixpoint_tree {Label : Type _} {prog : Program} {target_pc : BitVec 64}
    (cut_pc : Label → BitVec 64)
    (P_inv : Label → State → Nat → SepProp)
    (Inv : Label → State → Nat → Prop)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hstep : ∀ (l : Label) (s : State) (fuel : Nat),
      s.pc = cut_pc l → s.status = .Running → Inv l s fuel →
      SepWP.CFGStep prog target_pc cut_pc P_inv Inv post fuel (oom := oom) s (P_inv l s fuel))
    {l0 : Label} {s0 : State} {fuel : Nat} {P : SepProp}
    (hpc0 : s0.pc = cut_pc l0)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv l0 s0 fuel)
    (hinv0 : Inv l0 s0 fuel) :
    SepWP prog target_pc s0 P post oom := by
  apply SepWP.weaken_pre hent0
  suffices hmain : ∀ (f : Nat) (l : Label) (s : State),
      s.pc = cut_pc l → s.status = .Running → Inv l s f →
      SepWP prog target_pc s (P_inv l s f) post oom from
    hmain fuel l0 s0 hpc0 hrun0 hinv0
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro l s hpc hrun hinv
    exact (hstep l s f hpc hrun hinv).eval ih

/-- Step-indexed cutpoint fixpoint theorem (`SepProp` and `Prop` disjunction form).
    Given cutpoint labels `Label`, cutpoint PCs `cut_pc : Label → BitVec 64`, a spatial cutpoint
    invariant `P_inv : Label → State → Nat → SepProp`, and a pure ranking-indexed cutpoint
    invariant `Inv : Label → State → Nat → Prop`, if from every `(l, s, fuel)` satisfying
    `Inv l s fuel`:
    * either `SepWP prog target_pc s (P_inv l s fuel) post` holds (direct exit to `target_pc`),
    * or after consuming `1 ≤ steps ≤ fuel` of the ranking measure `fuel`, execution reaches `cut_pc l'`
      in a state `s'` with spatial resource `P' ⊢ P_inv l' s' (fuel - steps)` satisfying
      `Inv l' s' (fuel - steps)`,
    then `Inv l0 s0 fuel` implies `SepWP prog target_pc s0 P post` for all `fuel` by strong
    induction on `fuel`. -/
theorem SepWP.cfg_fixpoint_sep {Label : Type _} {prog : Program} {target_pc : BitVec 64}
    (cut_pc : Label → BitVec 64)
    (P_inv : Label → State → Nat → SepProp)
    (Inv : Label → State → Nat → Prop)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hstep : ∀ (l : Label) (s : State) (fuel : Nat),
      s.pc = cut_pc l → s.status = .Running → Inv l s fuel →
      SepWP prog target_pc s (P_inv l s fuel) post oom ∨
      ∃ (l' : Label) (steps : Nat), 1 ≤ steps ∧ steps ≤ fuel ∧
        SepWP prog (cut_pc l') s (P_inv l s fuel) (fun s' P' =>
          (P' ⊢ P_inv l' s' (fuel - steps)) ∧ Inv l' s' (fuel - steps)) oom)
    {l0 : Label} {s0 : State} {fuel : Nat} {P : SepProp}
    (hpc0 : s0.pc = cut_pc l0)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv l0 s0 fuel)
    (hinv0 : Inv l0 s0 fuel) :
    SepWP prog target_pc s0 P post oom := by
  refine SepWP.cfg_fixpoint_tree cut_pc P_inv Inv ?_ hpc0 hrun0 hent0 hinv0
  intro l s f hpc hrun hinv
  rcases hstep l s f hpc hrun hinv with hexit | ⟨l', steps, hpos, hle, hjump⟩
  · exact .exit hexit
  · exact .jump l' steps hpos hle hjump

/-- Specialization of `SepWP.cfg_fixpoint_sep` when the spatial invariant `P : SepProp` is uniform
    across cutpoints and step-indexed state transitions are tracked in `Inv : Label → State → Nat → Prop`. -/
theorem SepWP.cfg_fixpoint {Label : Type _} {prog : Program} {target_pc : BitVec 64}
    (cut_pc : Label → BitVec 64)
    (Inv : Label → State → Nat → Prop)
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hstep : ∀ (l : Label) (s : State) (fuel : Nat),
      s.pc = cut_pc l → s.status = .Running → Inv l s fuel →
      SepWP prog target_pc s P post oom ∨
      ∃ (l' : Label) (steps : Nat), 1 ≤ steps ∧ steps ≤ fuel ∧
        SepWP prog (cut_pc l') s P (sepPost (fun s' => Inv l' s' (fuel - steps)) P) oom)
    {l0 : Label} {s0 : State} {fuel : Nat}
    (hpc0 : s0.pc = cut_pc l0)
    (hrun0 : s0.status = .Running)
    (hinv0 : Inv l0 s0 fuel) :
    SepWP prog target_pc s0 P post oom := by
  refine SepWP.cfg_fixpoint_sep cut_pc (fun _ _ _ => P) Inv ?_ hpc0 hrun0 (Entails.refl P) hinv0
  intro l s f hpc hrun hinv
  rcases hstep l s f hpc hrun hinv with hexit | ⟨l', steps, hpos, hle, hjump⟩
  · exact Or.inl hexit
  · refine Or.inr ⟨l', steps, hpos, hle, SepWP.mono hjump ?_⟩
    intro s' P' _ _ ⟨hinv', hent⟩
    exact ⟨hent, hinv'⟩

/-! ### Step-Indexed Partial-Correctness (`wp_idx` / `SepWP_idx`) Cutpoint Fixpoint -/

/-- Monotonicity of `wp_idx` with respect to the postcondition `Q`. -/
theorem wp_idx.mono {prog : Program} {stop : State → Prop} {Q Q' : State → Prop}
    (himp : ∀ s, stop s → Q s → Q' s) :
    ∀ {n : Nat} {s : State}, wp_idx prog stop Q n s → wp_idx prog stop Q' n s
  | 0, _, _ => trivial
  | _ + 1, _, Or.inl ⟨hstop, hQ⟩ => Or.inl ⟨hstop, himp _ hstop hQ⟩
  | _ + 1, _, Or.inr ⟨hnstop, hrun, hstep, hnext⟩ =>
    Or.inr ⟨hnstop, hrun, hstep, fun s' hs' => wp_idx.mono himp (hnext s' hs')⟩

/-- Step-indexed reachability over `steps` machine transitions:
    * At `0` steps remaining: either `stop s ∧ Q s` or the target cutpoint predicate `M s` holds.
    * At `k + 1` steps remaining: either `stop s ∧ Q s` holds now, or `¬ stop s` holds, `s` is
      `.Running` and can take a `Step`, and every successor satisfies `wp_idx_to ... k s'`. -/
def wp_idx_to (prog : Program) (stop : State → Prop) (Q M : State → Prop) : Nat → State → Prop
  | 0,     s => (stop s ∧ Q s) ∨ M s
  | k + 1, s =>
    (stop s ∧ Q s) ∨
    (¬ stop s ∧ s.status = .Running ∧ (∃ s', Step prog s s') ∧
      ∀ s', Step prog s s' → wp_idx_to prog stop Q M k s')

/-- Monotonicity of `wp_idx_to` in the target predicate `M`. -/
theorem wp_idx_to.mono {prog : Program} {stop : State → Prop} {Q M M' : State → Prop}
    (himp : ∀ s, M s → M' s) :
    ∀ {k : Nat} {s : State}, wp_idx_to prog stop Q M k s → wp_idx_to prog stop Q M' k s
  | 0, _, Or.inl h => Or.inl h
  | 0, _, Or.inr hM => Or.inr (himp _ hM)
  | _ + 1, _, Or.inl h => Or.inl h
  | _ + 1, _, Or.inr ⟨hnstop, hrun, hex, hnext⟩ =>
    Or.inr ⟨hnstop, hrun, hex, fun s' hs' => wp_idx_to.mono himp (hnext s' hs')⟩

/-- Sequential composition of a `steps`-step `wp_idx_to` segment with a `(fuel - steps)`-step
    `wp_idx` continuation whenever `steps ≤ fuel`. -/
theorem wp_idx.bind_to {prog : Program} {stop : State → Prop} {Q M : State → Prop} :
    ∀ {steps fuel : Nat} {s : State},
      steps ≤ fuel →
      wp_idx_to prog stop Q M steps s →
      (∀ s', M s' → wp_idx prog stop Q (fuel - steps) s') →
      wp_idx prog stop Q fuel s
  | 0, fuel, s, _, h0, hcont => by
    rcases h0 with ⟨hstop, hQ⟩ | hM
    · cases fuel with
      | zero => trivial
      | succ _ => exact Or.inl ⟨hstop, hQ⟩
    · simpa using hcont s hM
  | _ + 1, 0, _, hle, _, _ => by omega
  | steps + 1, fuel + 1, s, hle, h, hcont => by
    rcases h with ⟨hstop, hQ⟩ | ⟨hnstop, hrun, hex, hnext⟩
    · exact Or.inl ⟨hstop, hQ⟩
    · refine Or.inr ⟨hnstop, hrun, hex, fun s' hs' => ?_⟩
      have heq : (fuel + 1) - (steps + 1) = fuel - steps := Nat.succ_sub_succ fuel steps
      exact wp_idx.bind_to (by omega) (hnext s' hs') (fun s'' hM => heq ▸ hcont s'' hM)

/-- Step-indexed cutpoint fixpoint theorem for `wp_idx`.
    Given a label type `Label` and step-indexed cutpoint invariant `Inv : Label → State → Nat → Prop`,
    if from every `(l, s, fuel)` satisfying `Inv l s fuel`, either `wp_idx prog stop Q fuel s`
    holds directly, or there exist `1 ≤ steps ≤ fuel` and `l'` such that within `steps` steps
    execution either stops with `Q` or reaches a state `s'` satisfying `Inv l' s' (fuel - steps)`
    (`wp_idx_to prog stop Q (fun s' => Inv l' s' (fuel - steps)) steps s`),
    then `Inv l0 s0 fuel → wp_idx prog stop Q fuel s0` holds for all `fuel`. -/
theorem wp_idx.cfg_fixpoint {Label : Type _} {prog : Program} {stop : State → Prop}
    {Q : State → Prop} (Inv : Label → State → Nat → Prop)
    (hstep : ∀ (l : Label) (s : State) (fuel : Nat),
      Inv l s fuel →
      wp_idx prog stop Q fuel s ∨
      ∃ (l' : Label) (steps : Nat), 1 ≤ steps ∧ steps ≤ fuel ∧
        wp_idx_to prog stop Q (fun s' => Inv l' s' (fuel - steps)) steps s)
    {l0 : Label} {s0 : State} {fuel : Nat}
    (hinv0 : Inv l0 s0 fuel) :
    wp_idx prog stop Q fuel s0 := by
  suffices hmain : ∀ (f : Nat) (l : Label) (s : State),
      Inv l s f → wp_idx prog stop Q f s from
    hmain fuel l0 s0 hinv0
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro l s hinv
    rcases hstep l s f hinv with hexit | ⟨l', steps, hpos, hle, hmid⟩
    · exact hexit
    · refine wp_idx.bind_to hle hmid ?_
      intro s' hinv'
      have hlt : f - steps < f := by omega
      exact ih (f - steps) hlt l' s' hinv'

/-! ## DAG join-point combinators -/

/-- Cut execution at a shared join PC `pc_join` with pure join assertion `J : State → Prop`
    and spatial join assertion `Q : SepProp`.
    The prefix proves `SepWP prog pc_join s P (sepPost J Q)` (whose spatial obligation `P_f ⊢ Q`
    is discharged by `wp_done`), and the continuation from `pc_join` to `target_pc` is proved
    only once with the concrete spatial context `Q`. -/
theorem SepWP.join {prog : Program} {pc_join target_pc : BitVec 64}
    (J : State → Prop) (Q : SepProp)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h_to_join : SepWP prog pc_join s P (sepPost J Q) oom)
    (h_from_join : ∀ sj : State, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj Q post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.seq h_to_join ?_
  intro sj Pj hpc_j hrun_j ⟨hJ, hent⟩
  exact SepWP.weaken_pre hent (h_from_join sj hpc_j hrun_j hJ)

/-- Cut execution at a shared join PC `pc_join` where the spatial join assertion `Q : State → SepProp`
    depends on the join state `sj`. -/
theorem SepWP.join_state {prog : Program} {pc_join target_pc : BitVec 64}
    (J : State → Prop) (Q : State → SepProp)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h_to_join : SepWP prog pc_join s P (sepPostState J Q) oom)
    (h_from_join : ∀ sj : State, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj (Q sj) post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.seq h_to_join ?_
  intro sj Pj hpc_j hrun_j ⟨hJ, hent⟩
  exact SepWP.weaken_pre hent (h_from_join sj hpc_j hrun_j hJ)

/-- Diamond branch-and-join combinator: when `s.pc = if c then pc1 else pc2`, both the `c` and `¬c`
    branches step to the shared join PC `pc_join` establishing `sepPost J Q`, and the suffix from
    `pc_join` to `target_pc` is proved only once. -/
theorem SepWP.ite_join {prog : Program} {pc_join target_pc : BitVec 64}
    (J : State → Prop) (Q : SepProp)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
    (hthen : c → SepWP prog pc_join (s.setPC pc1) P (sepPost J Q) oom)
    (helse : ¬ c → SepWP prog pc_join (s.setPC pc2) P (sepPost J Q) oom)
    (hjoin : ∀ sj : State, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj Q post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.join J Q (SepWP.ite hpc hthen helse) hjoin

/-- Logical case-split and join at `pc_join`: both `c` and `¬c` branches prove reachability to
    `pc_join` with `sepPost J Q`, and the suffix from `pc_join` to `target_pc` is proved once. -/
theorem SepWP.by_cases_join (c : Prop) {prog : Program} {pc_join target_pc : BitVec 64}
    (J : State → Prop) (Q : SepProp)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hthen : c → SepWP prog pc_join s P (sepPost J Q) oom)
    (helse : ¬ c → SepWP prog pc_join s P (sepPost J Q) oom)
    (hjoin : ∀ sj : State, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj Q post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.join J Q (by by_cases hc : c; exact hthen hc; exact helse hc) hjoin

/-- Cut at `pc_join` with pure join assertion `J : State → Prop`, preserving the current spatial
    context `P`. -/
theorem SepWP.join_same {prog : Program} {pc_join target_pc : BitVec 64}
    (J : State → Prop)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbranch : SepWP prog pc_join s P (sepPost J P) oom)
    (hjoin : ∀ sj : State, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.join J P hbranch hjoin

/-- Diamond branch-and-join combinator preserving the current spatial context `P`. -/
theorem SepWP.ite_join_same {prog : Program} {pc_join target_pc : BitVec 64}
    (J : State → Prop)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
    (hthen : c → SepWP prog pc_join (s.setPC pc1) P (sepPost J P) oom)
    (helse : ¬ c → SepWP prog pc_join (s.setPC pc2) P (sepPost J P) oom)
    (hjoin : ∀ sj : State, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.ite_join J P hpc hthen helse hjoin

end

public meta section

/-- Cut a `SepWP` goal at intermediate join PC `pc_join` with pure join invariant `J`
    (preserving the current spatial context `P`). Use `wp_join_sep` to specify a modified
    spatial context `Q`. -/
syntax "wp_join " term:max term:max : tactic
macro_rules
  | `(tactic| wp_join $pc_join $J) =>
    `(tactic| apply (SepWP.join_same (pc_join := $pc_join) $J))

/-- Cut a `SepWP` goal at intermediate join PC `pc_join` with pure join invariant `J` and
    spatial context `Q`. -/
syntax "wp_join_sep " term:max term:max term:max : tactic
macro_rules
  | `(tactic| wp_join_sep $pc_join $J $Q) =>
    `(tactic| apply (SepWP.join (pc_join := $pc_join) $J $Q))

section WpIfJoinTactic
open Lean Elab Tactic

/-- Split a conditional branch `s.pc = if c then pc1 else pc2` and reconverge both branches at
    `pc_join` with pure join invariant `J` (preserving the current spatial context `P`), leaving 3 subgoals:
    1. `then` branch to `pc_join`,
    2. `else` branch to `pc_join`,
    3. shared continuation from `pc_join` to `target_pc`. -/
syntax "wp_if_join " term:max term:max : tactic
elab_rules : tactic
  | `(tactic| wp_if_join $pc_join $J) => do
    let hId ← freshIdent `hcond
    evalTactic (← `(tactic| (
      apply (SepWP.ite_join_same (pc_join := $pc_join) $J)
      wp_focus_close wp_norm_lhs
    )))
    let gs ← getGoals
    match gs with
    | gThen :: gElse :: rest =>
      setGoals [gThen]
      evalTactic (← `(tactic| intro $hId:ident))
      normWpIfHyp hId
      evalTactic (← `(tactic| try wp_norm_state))
      let gsThen ← getGoals
      setGoals [gElse]
      evalTactic (← `(tactic| intro $hId:ident))
      normWpIfHyp hId
      evalTactic (← `(tactic| try wp_norm_state))
      let gsElse ← getGoals
      setGoals (gsThen ++ gsElse ++ rest)
    | _ => throwError "wp_if_join: unexpected subgoals"

/-- Split a conditional branch `s.pc = if c then pc1 else pc2` and reconverge both branches at
    `pc_join` with pure join invariant `J` and spatial context `Q`, leaving 3 subgoals. -/
syntax "wp_if_join_sep " term:max term:max term:max : tactic
elab_rules : tactic
  | `(tactic| wp_if_join_sep $pc_join $J $Q) => do
    let hId ← freshIdent `hcond
    evalTactic (← `(tactic| (
      apply (SepWP.ite_join (pc_join := $pc_join) $J $Q)
      wp_focus_close wp_norm_lhs
    )))
    let gs ← getGoals
    match gs with
    | gThen :: gElse :: rest =>
      setGoals [gThen]
      evalTactic (← `(tactic| intro $hId:ident))
      normWpIfHyp hId
      evalTactic (← `(tactic| try wp_norm_state))
      let gsThen ← getGoals
      setGoals [gElse]
      evalTactic (← `(tactic| intro $hId:ident))
      normWpIfHyp hId
      evalTactic (← `(tactic| try wp_norm_state))
      let gsElse ← getGoals
      setGoals (gsThen ++ gsElse ++ rest)
    | _ => throwError "wp_if_join_sep: unexpected subgoals"

end WpIfJoinTactic

end

@[expose] public section

/-! ## Structured, multi-exit, latch, and nested loop combinators -/

/-! ### Fuel-indexed loops -/

/-- Fuel-indexed natural loop combinator with state- and fuel-dependent spatial invariant
    `P_inv : Nat → State → SepProp` and pure invariant `Inv : Nat → State → Prop`.
    Specializes `SepWP.cfg_fixpoint_sep` to `Label = Unit`.
    At each state `st` at `head_pc` with fuel `fuel`:
    * either execution exits to `target_pc` (`Or.inl`),
    * or execution steps back to `head_pc` consuming `1 ≤ steps ≤ fuel` fuel (`Or.inr`). -/
theorem SepWP.loop_fuel_sep {prog : Program} {head_pc target_pc : BitVec 64}
    (P_inv : Nat → State → SepProp) (Inv : Nat → State → Prop)
    {s0 : State} {fuel : Nat} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv fuel s0)
    (hinv0 : Inv fuel s0)
    (hstep : ∀ (f : Nat) (st : State),
      st.pc = head_pc → st.status = .Running → Inv f st →
      SepWP prog target_pc st (P_inv f st) post oom ∨
      ∃ steps : Nat, 1 ≤ steps ∧ steps ≤ f ∧
        SepWP prog head_pc st (P_inv f st) (sepPostState (Inv (f - steps)) (P_inv (f - steps))) oom) :
    SepWP prog target_pc s0 P post oom := by
  refine SepWP.cfg_fixpoint_sep (Label := Unit) (fun _ => head_pc)
    (fun _ st f => P_inv f st) (fun _ st f => Inv f st) ?_ (l0 := ()) hpc0 hrun0 hent0 hinv0
  intro _ st f hpc hrun hinv
  rcases hstep f st hpc hrun hinv with hexit | ⟨steps, hpos, hle, hback⟩
  · exact Or.inl hexit
  · refine Or.inr ⟨(), steps, hpos, hle, SepWP.mono hback ?_⟩
    intro s' P' _ _ ⟨hinv', hent'⟩
    exact ⟨hent', hinv'⟩

/-- Fuel-indexed natural loop combinator with uniform spatial context `P : SepProp` and pure
    fuel-indexed invariant `Inv : Nat → State → Prop`.
    Supports variable step decrements `1 ≤ steps ≤ fuel` as well as mid-loop early exits to `target_pc`. -/
theorem SepWP.loop_fuel {prog : Program} {head_pc target_pc : BitVec 64}
    (Inv : Nat → State → Prop)
    {s0 : State} {fuel : Nat} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hinv0 : Inv fuel s0)
    (hstep : ∀ (f : Nat) (st : State),
      st.pc = head_pc → st.status = .Running → Inv f st →
      SepWP prog target_pc st P post oom ∨
      ∃ steps : Nat, 1 ≤ steps ∧ steps ≤ f ∧
        SepWP prog head_pc st P (sepPost (Inv (f - steps)) P) oom) :
    SepWP prog target_pc s0 P post oom :=
  SepWP.loop_fuel_sep (fun _ _ => P) Inv hpc0 hrun0 (Entails.refl P) hinv0 hstep

/-! ### Measure and countdown loops -/

/-- Measure-indexed loop combinator with automatic linear ghost-budget accounting
    (`step_cost * m + exit_cost ≤ fuel`, where `step_cost`, `exit_cost`, and `fuel` are ghost/arithmetic
    budget parameters threaded to `hbase` and `hstep`).
    Eliminates manual `obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + step_cost := ⟨fuel - step_cost, by omega⟩`
    and manual `SepWP.mono` plumbing:
    * At `m = 0`: given `exit_cost ≤ fuel` and `Inv 0 st`, execution reaches `target_pc`.
    * At `m + 1`: given `step_cost * (m + 1) + exit_cost ≤ fuel` and `Inv (m + 1) st`, execution
      either exits early to `target_pc` (`Or.inl`) or steps back to `head_pc` with measure `m` (`Or.inr`),
      and the remaining ghost budget `step_cost * m + exit_cost ≤ fuel - step_cost` is discharged
      automatically. -/
theorem SepWP.loop_measure_fuel {prog : Program} {head_pc target_pc : BitVec 64}
    (step_cost exit_cost : Nat)
    (P_inv : Nat → State → SepProp) (Inv : Nat → State → Prop)
    {s0 : State} {m fuel : Nat} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbudget0 : step_cost * m + exit_cost ≤ fuel)
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv m s0)
    (hinv0 : Inv m s0)
    (hbase : ∀ (f : Nat) (st : State),
      exit_cost ≤ f → st.pc = head_pc → st.status = .Running → Inv 0 st →
      SepWP prog target_pc st (P_inv 0 st) post oom)
    (hstep : ∀ (m' f : Nat) (st : State),
      step_cost * (m' + 1) + exit_cost ≤ f →
      st.pc = head_pc → st.status = .Running → Inv (m' + 1) st →
      SepWP prog target_pc st (P_inv (m' + 1) st) post oom ∨
      SepWP prog head_pc st (P_inv (m' + 1) st) (sepPostState (Inv m') (P_inv m')) oom) :
    SepWP prog target_pc s0 P post oom := by
  apply SepWP.weaken_pre hent0
  clear hent0
  induction m generalizing s0 fuel with
  | zero =>
    have hex : exit_cost ≤ fuel := by omega
    exact hbase fuel s0 hex hpc0 hrun0 hinv0
  | succ m' ih =>
    rcases hstep m' fuel s0 hbudget0 hpc0 hrun0 hinv0 with hexit | hback
    · exact hexit
    · refine SepWP.join_state (Inv m') (P_inv m') hback ?_
      intro s' hpc' hrun' hinv'
      have hbud' : step_cost * m' + exit_cost ≤ fuel - step_cost := by
        have hmul : step_cost * (m' + 1) = step_cost * m' + step_cost := Nat.mul_succ step_cost m'
        omega
      exact ih hbud' hpc' hrun' hinv'

/-- Measure / countdown loop combinator with state- and measure-dependent spatial invariant
    `P_inv : Nat → State → SepProp` and pure invariant `Inv : Nat → State → Prop`.
    Supports multiple exits:
    * Base exit (`m = 0`): `hbase` reaches `target_pc`.
    * Iteration step (`m = m' + 1`): `hstep` either exits early to `target_pc` (`Or.inl`, e.g. on a
      `break` / early `return` / hit condition) or branches back to `head_pc` with measure `m'` (`Or.inr`). -/
theorem SepWP.loop_measure_sep {prog : Program} {head_pc target_pc : BitVec 64}
    (P_inv : Nat → State → SepProp) (Inv : Nat → State → Prop)
    {s0 : State} {m : Nat} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv m s0)
    (hinv0 : Inv m s0)
    (hbase : ∀ st : State, st.pc = head_pc → st.status = .Running → Inv 0 st →
      SepWP prog target_pc st (P_inv 0 st) post oom)
    (hstep : ∀ (m' : Nat) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (m' + 1) st →
      SepWP prog target_pc st (P_inv (m' + 1) st) post oom ∨
      SepWP prog head_pc st (P_inv (m' + 1) st) (sepPostState (Inv m') (P_inv m')) oom) :
    SepWP prog target_pc s0 P post oom := by
  refine SepWP.loop_measure_fuel 1 0 P_inv Inv (fuel := m) (by omega)
    hpc0 hrun0 hent0 hinv0
    (fun _ st _ hpc hrun hinv => hbase st hpc hrun hinv)
    (fun m' _ st _ hpc hrun hinv => hstep m' st hpc hrun hinv)

/-- Measure / countdown loop combinator with a fixed spatial context `P : SepProp` and
    measure-indexed pure invariant `Inv : Nat → State → Prop`.
    Supports both base exits (`m = 0`) and mid-loop early exits (`Or.inl` at `m' + 1`). -/
theorem SepWP.loop_measure {prog : Program} {head_pc target_pc : BitVec 64}
    (Inv : Nat → State → Prop)
    {s0 : State} {m : Nat} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hinv0 : Inv m s0)
    (hbase : ∀ st : State, st.pc = head_pc → st.status = .Running → Inv 0 st →
      SepWP prog target_pc st P post oom)
    (hstep : ∀ (m' : Nat) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (m' + 1) st →
      SepWP prog target_pc st P post oom ∨
      SepWP prog head_pc st P (sepPost (Inv m') P) oom) :
    SepWP prog target_pc s0 P post oom :=
  SepWP.loop_measure_sep (fun _ _ => P) Inv hpc0 hrun0 (Entails.refl P) hinv0 hbase hstep

/-- Alias of `SepWP.loop_measure_sep` emphasizing multi-exit (`break` / early `return`) support. -/
abbrev SepWP.loop_multi_exit := @SepWP.loop_measure_sep

/-! ### List-cursor loops -/

/-- List-indexed loop combinator with spatial invariant `P_inv : List α → State → SepProp`
    and pure invariant `Inv : List α → State → Prop`.
    Proved via `SepWP.cfg_fixpoint_sep` using `xs.length` as the step-index fuel. -/
theorem SepWP.loop_list_sep {α : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (P_inv : List α → State → SepProp) (Inv : List α → State → Prop)
    {s0 : State} {xs : List α} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv xs s0)
    (hinv0 : Inv xs s0)
    (hnil : ∀ st : State, st.pc = head_pc → st.status = .Running → Inv [] st →
      SepWP prog target_pc st (P_inv [] st) post oom)
    (hcons : ∀ (x : α) (rest : List α) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (x :: rest) st →
      SepWP prog target_pc st (P_inv (x :: rest) st) post oom ∨
      SepWP prog head_pc st (P_inv (x :: rest) st) (sepPostState (Inv rest) (P_inv rest)) oom) :
    SepWP prog target_pc s0 P post oom := by
  refine SepWP.cfg_fixpoint_sep (Label := List α) (fun _ => head_pc)
    (fun l st _ => P_inv l st) (fun l st f => l.length = f ∧ Inv l st)
    ?_ hpc0 hrun0 hent0 ⟨rfl, hinv0⟩
  intro l st f hpc hrun ⟨hlen, hinv⟩
  cases l with
  | nil =>
    exact Or.inl (hnil st hpc hrun hinv)
  | cons x rest =>
    rcases hcons x rest st hpc hrun hinv with hexit | hback
    · exact Or.inl hexit
    · refine Or.inr ⟨rest, 1, by omega, by simp [← hlen], SepWP.mono hback ?_⟩
      intro s' P' _ _ ⟨hinv', hent'⟩
      refine ⟨hent', ?_, hinv'⟩
      simp at hlen
      omega

/-- List-indexed loop combinator with uniform spatial context `P : SepProp`. -/
theorem SepWP.loop_list {α : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (Inv : List α → State → Prop)
    {s0 : State} {xs : List α} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hinv0 : Inv xs s0)
    (hnil : ∀ st : State, st.pc = head_pc → st.status = .Running → Inv [] st →
      SepWP prog target_pc st P post oom)
    (hcons : ∀ (x : α) (rest : List α) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (x :: rest) st →
      SepWP prog target_pc st P post oom ∨
      SepWP prog head_pc st P (sepPost (Inv rest) P) oom) :
    SepWP prog target_pc s0 P post oom :=
  SepWP.loop_list_sep (fun _ _ => P) Inv hpc0 hrun0 (Entails.refl P) hinv0 hnil hcons

/-! ### Two-cutpoint header and latch loops -/

/-- Cutpoint labels for a loop with a main header (`head`) and a separate step latch (`latch`)
    in distinct blocks (e.g. a header at `+0x2c` and a latch at `+0x20` that branches back to it). -/
inductive CFGLabel2 (α : Type _) where
  | head (x : α)
  | latch (x : α)

/-- Two-cutpoint (`head_pc` + `latch_pc`) measure-indexed loop combinator, proved as an instance
    of `SepWP.cfg_fixpoint_sep` over `CFGLabel2 Nat` with step-index `fuel = 2 * m + 1` at
    `head m` and `fuel = 2 * m` at `latch m`:
    * At `head_pc` with measure `m`: execution either exits early to `target_pc` (`Or.inl`, e.g.,
      empty slot or key hit) or reaches `latch_pc` (`Or.inr`, e.g., occupied key miss or tombstone).
    * At `latch_pc` with `m = 0`: execution exits to `target_pc` (e.g., probe count exhausted).
    * At `latch_pc` with `m = m' + 1`: execution steps back to `head_pc` with measure `m'`. -/
theorem SepWP.loop_latch {prog : Program} {head_pc latch_pc target_pc : BitVec 64}
    (P_head P_latch : Nat → State → SepProp)
    (Inv_head Inv_latch : Nat → State → Prop)
    {s0 : State} {m : Nat} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_head m s0)
    (hinv0 : Inv_head m s0)
    (h_head : ∀ (k : Nat) (st : State),
      st.pc = head_pc → st.status = .Running → Inv_head k st →
      SepWP prog target_pc st (P_head k st) post oom ∨
      SepWP prog latch_pc st (P_head k st) (sepPostState (Inv_latch k) (P_latch k)) oom)
    (h_latch_zero : ∀ st : State,
      st.pc = latch_pc → st.status = .Running → Inv_latch 0 st →
      SepWP prog target_pc st (P_latch 0 st) post oom)
    (h_latch_succ : ∀ (k : Nat) (st : State),
      st.pc = latch_pc → st.status = .Running → Inv_latch (k + 1) st →
      SepWP prog head_pc st (P_latch (k + 1) st) (sepPostState (Inv_head k) (P_head k)) oom) :
    SepWP prog target_pc s0 P post oom := by
  let cut_pc : CFGLabel2 Nat → BitVec 64
    | .head _ => head_pc
    | .latch _ => latch_pc
  let P_inv : CFGLabel2 Nat → State → Nat → SepProp
    | .head k, st, _ => P_head k st
    | .latch k, st, _ => P_latch k st
  let Inv : CFGLabel2 Nat → State → Nat → Prop
    | .head k, st, f => f = 2 * k + 1 ∧ Inv_head k st
    | .latch k, st, f => f = 2 * k ∧ Inv_latch k st
  refine SepWP.cfg_fixpoint_sep cut_pc P_inv Inv ?_ (l0 := .head m) (fuel := 2 * m + 1)
    hpc0 hrun0 hent0 ⟨rfl, hinv0⟩
  intro l st f hpc hrun hinv
  cases l with
  | head k =>
    rcases hinv with ⟨hf, hinv_h⟩
    rcases h_head k st hpc hrun hinv_h with hexit | hlatch
    · exact Or.inl hexit
    · refine Or.inr ⟨.latch k, 1, by omega, by omega, SepWP.mono hlatch ?_⟩
      intro s' P' _ _ ⟨hinv_l, hent_l⟩
      exact ⟨hent_l, by omega, hinv_l⟩
  | latch k =>
    rcases hinv with ⟨hf, hinv_l⟩
    cases k with
    | zero =>
      exact Or.inl (h_latch_zero st hpc hrun hinv_l)
    | succ k' =>
      refine Or.inr ⟨.head k', 1, by omega, by omega, SepWP.mono (h_latch_succ k' st hpc hrun hinv_l) ?_⟩
      intro s' P' _ _ ⟨hinv_h, hent_h⟩
      exact ⟨hent_h, by omega, hinv_h⟩

/-! ### Nested loops -/

/-- Nested loop combinator composing an outer measure-indexed loop at `outer_pc` with an inner
    execution phase from `inner_pc` to `inner_exit_pc` (e.g., an inner `SepWP.loop_measure` or
    `SepWP.loop_latch` invocation) followed by an outer latch transition from `inner_exit_pc`
    back to `outer_pc`:
    * At `m = 0`: `h_outer_done` exits from `outer_pc` to `target_pc`.
    * At `m + 1`: `h_to_inner` transitions from `outer_pc` to either `target_pc` (early exit),
      `outer_pc` directly (skipping the inner loop), or `inner_pc`; `h_inner` executes the inner
      loop from `inner_pc` to `inner_exit_pc`; and `h_from_inner` transitions from `inner_exit_pc`
      back to `outer_pc` with measure `m`. -/
theorem SepWP.nested_loop {prog : Program}
    {outer_pc inner_pc inner_exit_pc target_pc : BitVec 64}
    (P_outer P_inner P_inner_exit : Nat → State → SepProp)
    (Inv_outer Inv_inner Inv_inner_exit : Nat → State → Prop)
    {s0 : State} {m : Nat} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc0 : s0.pc = outer_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_outer m s0)
    (hinv0 : Inv_outer m s0)
    (h_outer_done : ∀ st : State,
      st.pc = outer_pc → st.status = .Running → Inv_outer 0 st →
      SepWP prog target_pc st (P_outer 0 st) post oom)
    (h_to_inner : ∀ (k : Nat) (st : State),
      st.pc = outer_pc → st.status = .Running → Inv_outer (k + 1) st →
      SepWP prog target_pc st (P_outer (k + 1) st) post oom ∨
      SepWP prog outer_pc st (P_outer (k + 1) st) (sepPostState (Inv_outer k) (P_outer k)) oom ∨
      SepWP prog inner_pc st (P_outer (k + 1) st) (sepPostState (Inv_inner k) (P_inner k)) oom)
    (h_inner : ∀ (k : Nat) (st : State),
      st.pc = inner_pc → st.status = .Running → Inv_inner k st →
      SepWP prog inner_exit_pc st (P_inner k st) (sepPostState (Inv_inner_exit k) (P_inner_exit k)) oom)
    (h_from_inner : ∀ (k : Nat) (st : State),
      st.pc = inner_exit_pc → st.status = .Running → Inv_inner_exit k st →
      SepWP prog outer_pc st (P_inner_exit k st) (sepPostState (Inv_outer k) (P_outer k)) oom) :
    SepWP prog target_pc s0 P post oom := by
  refine SepWP.loop_measure_sep P_outer Inv_outer hpc0 hrun0 hent0 hinv0 h_outer_done ?_
  intro k st hpc hrun hinv
  rcases h_to_inner k st hpc hrun hinv with hexit | hskip | hgo_inner
  · exact Or.inl hexit
  · exact Or.inr hskip
  · refine Or.inr (SepWP.join_state (Inv_inner k) (P_inner k) hgo_inner ?_)
    intro si hpci hruni hinvi
    refine SepWP.join_state (Inv_inner_exit k) (P_inner_exit k)
      (h_inner k si hpci hruni hinvi) ?_
    intro se hpce hrune hinve
    exact h_from_inner k se hpce hrune hinve

/-! ## Framed `sepPost` helpers and CPS loop combinators -/

attribute [local semireducible] SepWP

/-- Frame a `sepPost` specification with an invariant spatial resource `F`. -/
theorem SepWP.frame_sepPost {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q F : SepProp} {Inv : State → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P (sepPost Inv Q) oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; first | (try rw [emp_sepConj] at ho); exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWP prog target_pc s (P ∗ F) (sepPost Inv (Q ∗ F)) oom := by
  intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_mono (h (F ∗ R) hm) ?_ (fun sf hoom_st hmo => hoom sf R hoom_st hmo)
  rintro sf _ _ ⟨P1, hmf, hInv, hQ⟩
  rw [← sepConj_assoc] at hmf
  exact ⟨P1 ∗ F, hmf, hInv, sepConj_mono_left hQ⟩

/-- Sequence a `sepPost` step to `mid_pc` with a continuation to `target_pc`, framing `F`. -/
theorem SepWP.bind_sepPost {prog : Program} {mid_pc target_pc : BitVec 64} {s : State}
    {P P1 Q1 F : SepProp} {Inv1 : State → Prop} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : SepWP prog mid_pc s P1 (sepPost Inv1 Q1) oom)
    (hpre : P ⊢ P1 ∗ F)
    (h2 : ∀ s1 : State, s1.pc = mid_pc → s1.status = .Running → Inv1 s1 →
      SepWP prog target_pc s1 (Q1 ∗ F) post oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; first | (try rw [emp_sepConj] at ho); exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.weaken_pre hpre
  refine SepWP.seq (SepWP.frame_sepPost h1 (F := F) hoom) ?_
  intro s1 P_m hpc1 hrun1 ⟨hInv1, hent1⟩
  exact SepWP.weaken_pre hent1 (h2 s1 hpc1 hrun1 hInv1)

/-- Close a `sepPost` goal at `target_pc` from a framed `sepPost` step to the same `target_pc`. -/
theorem SepWP.done_sepPost {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P1 Q1 F Q : SepProp} {Inv1 Inv : State → Prop} {oom : State → SepProp}
    (h1 : SepWP prog target_pc s P1 (sepPost Inv1 Q1) oom)
    (hpre : P ⊢ P1 ∗ F)
    (himp : ∀ sf : State, sf.pc = target_pc → sf.status = .Running → Inv1 sf → Inv sf)
    (hpost : Q1 ∗ F ⊢ Q)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; first | (try rw [emp_sepConj] at ho); exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWP prog target_pc s P (sepPost Inv Q) oom := by
  apply SepWP.weaken_pre hpre
  refine SepWP.mono (SepWP.frame_sepPost h1 (F := F) hoom) ?_
  intro sf P_f hpc hrun ⟨hInv1, hent1⟩
  exact ⟨himp sf hpc hrun hInv1, Entails.trans hent1 hpost⟩

/-- Well-founded ghost-state loop combinator with a single-goal step obligation and an
    in-context back-edge continuation. Supports arbitrary ghost state `G`, state-aware measure
    `meas : G → State → Nat`, mid-loop early exits, and ghost-indexed postconditions. -/
theorem SepWP.loop_wf {G : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (meas : G → State → Nat)
    (P_inv : G → State → SepProp)
    (Inv : G → State → Prop)
    (post : G → State → SepProp → Prop)
    {oom : State → SepProp}
    {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv g0 s0)
    (hinv0 : Inv g0 s0)
    (hstep : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv g st →
      (∀ (g' : G) (st' : State), meas g' st' < meas g st →
        st'.pc = head_pc → st'.status = .Running → Inv g' st' →
        SepWP prog target_pc st' (P_inv g' st') (post g') oom) →
      SepWP prog target_pc st (P_inv g st) (post g) oom) :
    SepWP prog target_pc s0 P (post g0) oom := by
  apply SepWP.weaken_pre hent0
  suffices h : ∀ (n : Nat) (g : G) (st : State), meas g st = n →
      st.pc = head_pc → st.status = .Running → Inv g st →
      SepWP prog target_pc st (P_inv g st) (post g) oom from
    h (meas g0 s0) g0 s0 rfl hpc0 hrun0 hinv0
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g st hn hpc hrun hinv
    refine hstep g st hpc hrun hinv ?_
    intro g' st' hlt hpc' hrun' hinv'
    exact ih (meas g' st') (hn ▸ hlt) g' st' rfl hpc' hrun' hinv'

/-- Specialization of `SepWP.loop_wf` for loops with a ghost-independent exit postcondition
    `post : State → SepProp → Prop`. -/
theorem SepWP.loop_wf_simple {G : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (meas : G → State → Nat)
    (P_inv : G → State → SepProp)
    (Inv : G → State → Prop)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv g0 s0)
    (hinv0 : Inv g0 s0)
    (hstep : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv g st →
      (∀ (g' : G) (st' : State), meas g' st' < meas g st →
        st'.pc = head_pc → st'.status = .Running → Inv g' st' →
        SepWP prog target_pc st' (P_inv g' st') post oom) →
      SepWP prog target_pc st (P_inv g st) post oom) :
    SepWP prog target_pc s0 P post oom :=
  SepWP.loop_wf meas P_inv Inv (fun _ => post) hpc0 hrun0 hent0 hinv0 hstep

/-- Apply an in-context back-edge continuation `next` at `head_pc`, optionally peeling a
    spatial frame `F_peel` (defaulting to `emp`) across the remaining iterations and re-joining it
    into `post_cur` on return. -/
theorem SepWP.loop_back {G : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    {meas : G → State → Nat} {P_inv : G → State → SepProp} {Inv : G → State → Prop}
    {post : G → State → SepProp → Prop} {post_cur : State → SepProp → Prop} {oom : State → SepProp}
    {n : Nat} {st' : State} {P_cur : SepProp}
    (next : ∀ (g' : G) (st' : State), meas g' st' < n →
      st'.pc = head_pc → st'.status = .Running → Inv g' st' →
      SepWP prog target_pc st' (P_inv g' st') (post g') oom)
    (g' : G)
    (hlt : meas g' st' < n)
    (hpc : st'.pc = head_pc) (hrun : st'.status = .Running) (hinv : Inv g' st')
    (F_peel : SepProp := emp)
    (hpre : P_cur ⊢ P_inv g' st' ∗ F_peel := by (try rw [sepConj_emp]); sep_frame)
    (hpost : ∀ sf P_f, sf.pc = target_pc → sf.status = .Running →
      post g' sf P_f → post_cur sf (P_f ∗ F_peel) := by
      intro sf P_f _ _ h; (try rw [sepConj_emp]); exact h)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F_peel ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; first | (try rw [emp_sepConj] at ho); exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWP prog target_pc st' P_cur post_cur oom := by
  apply SepWP.weaken_pre hpre
  intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_mono (next g' st' hlt hpc hrun hinv (F_peel ∗ R) hm) ?_
    (fun sf hoom_st hmo => hoom sf R hoom_st hmo)
  rintro sf hpcf hrunf ⟨P1, hmf, hpost'⟩
  rw [← sepConj_assoc] at hmf
  exact ⟨P1 ∗ F_peel, hmf, hpost sf P1 hpcf hrunf hpost'⟩

/-- Bounded counter / stride loop combinator over remaining iterations `rem : Nat`
    and evolving ghost state `g : G` in CPS form with a single-goal step obligation. -/
theorem SepWP.loop_nat_cps {G : Type _} {prog : Program} {head_pc ret_pc : BitVec 64}
    (P_inv : Nat → G → State → SepProp)
    (Inv : Nat → G → State → Prop)
    (post : Nat → G → State → SepProp → Prop)
    {oom : State → SepProp}
    {rem0 : Nat} {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv rem0 g0 s0)
    (hinv0 : Inv rem0 g0 s0)
    (hzero : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv 0 g st →
      SepWP prog ret_pc st (P_inv 0 g st) (post 0 g) oom)
    (hsucc : ∀ (k : Nat) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (k + 1) g st →
      (∀ (g' : G) (st' : State),
        st'.pc = head_pc → st'.status = .Running → Inv k g' st' →
        SepWP prog ret_pc st' (P_inv k g' st') (post k g') oom) →
      SepWP prog ret_pc st (P_inv (k + 1) g st) (post (k + 1) g) oom) :
    SepWP prog ret_pc s0 P (post rem0 g0) oom := by
  apply SepWP.weaken_pre hent0
  suffices h : ∀ (rem : Nat) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv rem g st →
      SepWP prog ret_pc st (P_inv rem g st) (post rem g) oom from
    h rem0 g0 s0 hpc0 hrun0 hinv0
  intro rem
  induction rem with
  | zero => exact hzero
  | succ k ih =>
    intro g st hpc hrun hinv
    exact hsucc k g st hpc hrun hinv ih

/-- List-cursor loop combinator with ghost state `G`, mid-loop early exits, and automatic
    return-path spatial frame peeling (`F_peel`). -/
theorem SepWP.loop_list_peel_cps {α G : Type _} {prog : Program} {head_pc ret_pc : BitVec 64}
    (P_inv : List α → G → State → SepProp)
    (Inv : List α → G → State → Prop)
    (post : List α → G → State → SepProp → Prop)
    {oom : State → SepProp}
    {xs0 : List α} {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv xs0 g0 s0)
    (hinv0 : Inv xs0 g0 s0)
    (hnil : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv [] g st →
      SepWP prog ret_pc st (P_inv [] g st) (post [] g) oom)
    (hcons : ∀ (x : α) (rest : List α) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (x :: rest) g st →
      (∀ (g' : G) (st' : State) {P_cur : SepProp} (F_peel : SepProp),
        st'.pc = head_pc → st'.status = .Running → Inv rest g' st' →
        (P_cur ⊢ P_inv rest g' st' ∗ F_peel) →
        (∀ sf P_f, sf.pc = ret_pc → sf.status = .Running →
          post rest g' sf P_f → post (x :: rest) g sf (P_f ∗ F_peel)) →
        SepWP prog ret_pc st' P_cur (post (x :: rest) g) oom) →
      SepWP prog ret_pc st (P_inv (x :: rest) g st) (post (x :: rest) g) oom)
    (hoom : ∀ sf F_peel R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F_peel ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ _ ho; first | (try rw [emp_sepConj] at ho); exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWP prog ret_pc s0 P (post xs0 g0) oom := by
  apply SepWP.weaken_pre hent0
  suffices h : ∀ (xs : List α) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv xs g st →
      SepWP prog ret_pc st (P_inv xs g st) (post xs g) oom from
    h xs0 g0 s0 hpc0 hrun0 hinv0
  intro xs
  induction xs with
  | nil => exact hnil
  | cons x rest ih =>
    intro g st hpc hrun hinv
    refine hcons x rest g st hpc hrun hinv ?_
    intro g' st' P_cur F_peel hpc' hrun' hinv' hpre hpost
    apply SepWP.weaken_pre hpre
    intro R hm
    rw [sepConj_assoc] at hm
    refine reaches_pc_mono (ih g' st' hpc' hrun' hinv' (F_peel ∗ R) hm) ?_
      (fun sf hoom_st hmo => hoom sf F_peel R hoom_st hmo)
    rintro sf hpcf hrunf ⟨P1, hmf, hpost'⟩
    rw [← sepConj_assoc] at hmf
    exact ⟨P1 ∗ F_peel, hmf, hpost sf P1 hpcf hrunf hpost'⟩

/-- Two-cutpoint (`head_pc` + `latch_pc`) non-empty list-cursor loop combinator with functional
    accumulator `step : α → G → G` and return-path spatial frame peeling `F_peel : α → G → SepProp`. -/
theorem SepWP.loop_list_peel_latch {α G : Type _} {prog : Program}
    {head_pc latch_pc exit_pc : BitVec 64}
    (step : α → G → G)
    (P_head : α → List α → G → SepProp)
    (P_latch : α → List α → G → SepProp)
    (F_peel : α → G → SepProp)
    (Q_out : List α → G → SepProp)
    (Inv_head : α → List α → G → State → Prop)
    (Inv_latch : α → List α → G → State → Prop)
    (Post_out : List α → G → State → Prop)
    {oom : State → SepProp}
    (hbody : ∀ (x : α) (rest : List α) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv_head x rest g st →
      SepWP prog latch_pc st (P_head x rest g)
        (sepPost (Inv_latch x rest (step x g)) (P_latch x rest (step x g))) oom)
    (hlatch_nil : ∀ (x : α) (g : G) (sm : State),
      sm.pc = latch_pc → sm.status = .Running → Inv_latch x [] (step x g) sm →
      SepWP prog exit_pc sm (P_latch x [] (step x g))
        (sepPost (Post_out [x] g) (Q_out [x] g)) oom)
    (hlatch_cons : ∀ (x y : α) (rest : List α) (g : G) (sm : State),
      sm.pc = latch_pc → sm.status = .Running → Inv_latch x (y :: rest) (step x g) sm →
      SepWP prog head_pc sm (P_latch x (y :: rest) (step x g))
        (sepPost (Inv_head y rest (step x g))
          (P_head y rest (step x g) ∗ F_peel x g)) oom)
    (hreassemble : ∀ (x y : α) (rest : List α) (g : G),
      Q_out (y :: rest) (step x g) ∗ F_peel x g ⊢ Q_out (x :: y :: rest) g)
    (hpost_imp : ∀ (x y : α) (rest : List α) (g : G) (sf : State),
      Post_out (y :: rest) (step x g) sf → Post_out (x :: y :: rest) g sf)
    (hoom : ∀ sf x g R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F_peel x g ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ _ _ ho; first | (try rw [emp_sepConj] at ho); exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    ∀ (x : α) (rest : List α) (g : G) (s0 : State),
      s0.pc = head_pc → s0.status = .Running → Inv_head x rest g s0 →
      SepWP prog exit_pc s0 (P_head x rest g)
        (sepPost (Post_out (x :: rest) g) (Q_out (x :: rest) g)) oom := by
  intro x rest
  induction rest generalizing x with
  | nil =>
    intro g s0 hpc0 hrun0 hinv0
    refine SepWP.bind_sepPost (hbody x [] g s0 hpc0 hrun0 hinv0) (F := emp)
      (by rw [sepConj_emp]; exact Entails.refl _) ?_
    intro sm hpcm hrunm hinvm
    rw [sepConj_emp]
    exact hlatch_nil x g sm hpcm hrunm hinvm
  | cons y rest' ih =>
    intro g s0 hpc0 hrun0 hinv0
    refine SepWP.bind_sepPost (hbody x (y :: rest') g s0 hpc0 hrun0 hinv0) (F := emp)
      (by rw [sepConj_emp]; exact Entails.refl _) ?_
    intro sm hpcm hrunm hinvm
    rw [sepConj_emp]
    refine SepWP.bind_sepPost (hlatch_cons x y rest' g sm hpcm hrunm hinvm) (F := emp)
      (by rw [sepConj_emp]; exact Entails.refl _) ?_
    intro s_next hpc_next hrun_next hinv_next
    rw [sepConj_emp]
    exact SepWP.done_sepPost (ih y (step x g) s_next hpc_next hrun_next hinv_next)
      (F := F_peel x g) (Entails.refl _)
      (fun sf _ _ hp => hpost_imp x y rest' g sf hp)
      (hreassemble x y rest' g)
      (fun sf R' hoom_st hmo => hoom sf x g R' hoom_st hmo)

/-- Multi-cutpoint well-founded CFG fixpoint combinator with an in-context cutpoint transition
    continuation and state-aware measure `meas : Label → State → Nat`. -/
theorem SepWP.cfg_fixpoint_wf_cps {Label : Type _} {prog : Program} {ret_pc : BitVec 64}
    (cut_pc : Label → BitVec 64)
    (meas : Label → State → Nat)
    (P_inv : Label → State → SepProp)
    (Inv : Label → State → Prop)
    (post : Label → State → SepProp → Prop)
    {oom : State → SepProp}
    {l0 : Label} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = cut_pc l0)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv l0 s0)
    (hinv0 : Inv l0 s0)
    (hstep : ∀ (l : Label) (st : State),
      st.pc = cut_pc l → st.status = .Running → Inv l st →
      (∀ (l' : Label) (st' : State), meas l' st' < meas l st →
        st'.pc = cut_pc l' → st'.status = .Running → Inv l' st' →
        SepWP prog ret_pc st' (P_inv l' st') (post l') oom) →
      SepWP prog ret_pc st (P_inv l st) (post l) oom) :
    SepWP prog ret_pc s0 P (post l0) oom := by
  apply SepWP.weaken_pre hent0
  suffices h : ∀ (n : Nat) (l : Label) (st : State), meas l st = n →
      st.pc = cut_pc l → st.status = .Running → Inv l st →
      SepWP prog ret_pc st (P_inv l st) (post l) oom from
    h (meas l0 s0) l0 s0 rfl hpc0 hrun0 hinv0
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l st hn hpc hrun hinv
    refine hstep l st hpc hrun hinv ?_
    intro l' st' hlt hpc' hrun' hinv'
    exact ih (meas l' st') (hn ▸ hlt) l' st' rfl hpc' hrun' hinv'

end

end ProofLib
