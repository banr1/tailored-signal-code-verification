/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.CFG
import Arm64.Trusted.Spec.SepLogic

/-!
# Loop Combinator Tactics

Framed loop combinators (`SepWP.loop_measure_framed`, `SepWP.loop_list_framed`,
`SepWP.nested_loop_simple`) that thread `LoopFrame` preservation automatically, together with
the `wp_loop_measure`, `wp_loop_list`, and `wp_nested_loop` tactics. Each tactic discharges
`pc` and `status` side goals, attempts initial entailment and invariant conjuncts, and introduces
tagged per-iteration goals (`base`/`step`, `nil`/`cons`, or `done`/`enter`/`inner`/`latch`).
-/

namespace ProofLib

open Arm64

@[expose] public section

/-! ## Framed and Fixed-Context Combinators -/

/-- Registers a loop body must not change, relative to the loop-entry state `s`: the stack
    pointer, the link register and the callee-saved registers. -/
abbrev LoopFrame (s st : State) : Prop :=
  st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st

/-- `SepWP.loop_measure_sep` whose invariant is strengthened with `LoopFrame s0 st`, so the
    caller's `Inv` does not need to restate stack-pointer, link-register and callee-saved
    preservation. -/
theorem SepWP.loop_measure_framed {prog : Program} {head_pc target_pc : BitVec 64}
    (P_inv : Nat → State → SepProp) (Inv : Nat → State → Prop)
    {s0 : State} {m : Nat} {P : SepProp} {post : State → SepProp → Prop}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv m s0)
    (hinv0 : Inv m s0)
    (hbase : ∀ st : State, st.pc = head_pc → st.status = .Running →
      Inv 0 st ∧ LoopFrame s0 st →
      SepWP prog target_pc st (P_inv 0 st) post)
    (hstep : ∀ (m' : Nat) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (m' + 1) st ∧ LoopFrame s0 st →
      SepWP prog target_pc st (P_inv (m' + 1) st) post ∨
      SepWP prog head_pc st (P_inv (m' + 1) st)
        (sepPostState (fun st' => Inv m' st' ∧ LoopFrame s0 st') (P_inv m'))) :
    SepWP prog target_pc s0 P post :=
  SepWP.loop_measure_sep P_inv (fun k st => Inv k st ∧ LoopFrame s0 st) hpc0 hrun0 hent0
    ⟨hinv0, rfl, rfl, CalleeSavedPreserved.rfl s0⟩ hbase hstep

/-- `SepWP.loop_list_sep` whose invariant is strengthened with `LoopFrame s0 st`. -/
theorem SepWP.loop_list_framed {α : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (P_inv : List α → State → SepProp) (Inv : List α → State → Prop)
    {s0 : State} {xs : List α} {P : SepProp} {post : State → SepProp → Prop}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv xs s0)
    (hinv0 : Inv xs s0)
    (hnil : ∀ st : State, st.pc = head_pc → st.status = .Running →
      Inv [] st ∧ LoopFrame s0 st →
      SepWP prog target_pc st (P_inv [] st) post)
    (hcons : ∀ (x : α) (rest : List α) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (x :: rest) st ∧ LoopFrame s0 st →
      SepWP prog target_pc st (P_inv (x :: rest) st) post ∨
      SepWP prog head_pc st (P_inv (x :: rest) st)
        (sepPostState (fun st' => Inv rest st' ∧ LoopFrame s0 st') (P_inv rest))) :
    SepWP prog target_pc s0 P post :=
  SepWP.loop_list_sep P_inv (fun l st => Inv l st ∧ LoopFrame s0 st) hpc0 hrun0 hent0
    ⟨hinv0, rfl, rfl, CalleeSavedPreserved.rfl s0⟩ hnil hcons

/-- `SepWP.loop_measure_framed` with one fixed spatial context `P`. -/
theorem SepWP.loop_measure_framed_simple {prog : Program} {head_pc target_pc : BitVec 64}
    (Inv : Nat → State → Prop)
    {s0 : State} {m : Nat} {P : SepProp} {post : State → SepProp → Prop}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hinv0 : Inv m s0)
    (hbase : ∀ st : State, st.pc = head_pc → st.status = .Running →
      Inv 0 st ∧ LoopFrame s0 st →
      SepWP prog target_pc st P post)
    (hstep : ∀ (m' : Nat) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (m' + 1) st ∧ LoopFrame s0 st →
      SepWP prog target_pc st P post ∨
      SepWP prog head_pc st P (sepPost (fun st' => Inv m' st' ∧ LoopFrame s0 st') P)) :
    SepWP prog target_pc s0 P post :=
  SepWP.loop_measure_framed (fun _ _ => P) Inv hpc0 hrun0 (Entails.refl P) hinv0 hbase hstep

/-- `SepWP.loop_list_framed` with one fixed spatial context `P`. -/
theorem SepWP.loop_list_framed_simple {α : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (Inv : List α → State → Prop)
    {s0 : State} {xs : List α} {P : SepProp} {post : State → SepProp → Prop}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hinv0 : Inv xs s0)
    (hnil : ∀ st : State, st.pc = head_pc → st.status = .Running →
      Inv [] st ∧ LoopFrame s0 st →
      SepWP prog target_pc st P post)
    (hcons : ∀ (x : α) (rest : List α) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (x :: rest) st ∧ LoopFrame s0 st →
      SepWP prog target_pc st P post ∨
      SepWP prog head_pc st P (sepPost (fun st' => Inv rest st' ∧ LoopFrame s0 st') P)) :
    SepWP prog target_pc s0 P post :=
  SepWP.loop_list_framed (fun _ _ => P) Inv hpc0 hrun0 (Entails.refl P) hinv0 hnil hcons

/-- `SepWP.nested_loop` with one fixed spatial context `P` at every cutpoint. -/
theorem SepWP.nested_loop_simple {prog : Program}
    {outer_pc inner_pc inner_exit_pc target_pc : BitVec 64}
    (Inv_outer Inv_inner Inv_inner_exit : Nat → State → Prop)
    {s0 : State} {m : Nat} {P : SepProp} {post : State → SepProp → Prop}
    (hpc0 : s0.pc = outer_pc)
    (hrun0 : s0.status = .Running)
    (hinv0 : Inv_outer m s0)
    (h_outer_done : ∀ st : State,
      st.pc = outer_pc → st.status = .Running → Inv_outer 0 st →
      SepWP prog target_pc st P post)
    (h_to_inner : ∀ (k : Nat) (st : State),
      st.pc = outer_pc → st.status = .Running → Inv_outer (k + 1) st →
      SepWP prog target_pc st P post ∨
      SepWP prog outer_pc st P (sepPost (Inv_outer k) P) ∨
      SepWP prog inner_pc st P (sepPost (Inv_inner k) P))
    (h_inner : ∀ (k : Nat) (st : State),
      st.pc = inner_pc → st.status = .Running → Inv_inner k st →
      SepWP prog inner_exit_pc st P (sepPost (Inv_inner_exit k) P))
    (h_from_inner : ∀ (k : Nat) (st : State),
      st.pc = inner_exit_pc → st.status = .Running → Inv_inner_exit k st →
      SepWP prog outer_pc st P (sepPost (Inv_outer k) P)) :
    SepWP prog target_pc s0 P post :=
  SepWP.nested_loop (fun _ _ => P) (fun _ _ => P) (fun _ _ => P)
    Inv_outer Inv_inner Inv_inner_exit hpc0 hrun0 (Entails.refl P) hinv0
    h_outer_done h_to_inner h_inner h_from_inner

end

/-! ## Tactic Front-Ends -/

public meta section

open Lean Elab Tactic Meta

private def loopRunOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  tac
  getGoals

private def loopCloseHeader : TacticM Unit := do
  evalTactic (← `(tactic| wp_focus_close wp_norm_lhs))

private def loopInitCap : Nat := 20000

private def loopTryCapped (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  match ← tryTacticCatchRuntime (withHeartbeatCap loopInitCap do tac; done) with
  | some _ => return []
  | none => return [g]

private def loopTryCloseEnt : TacticM Unit := do
  let g ← getMainGoal
  setGoals (← loopTryCapped g (evalTactic (← `(tactic|
    first
    | exact Entails.refl _
    | (try dsimp only
       try simp (config := { decide := true }) only [
         sepConj_assoc, emp_sepConj, sepConj_emp, wp_norm, arm64_norm, *]
       first
       | exact Entails.refl _
       | exact Entails.of_eq
       | sep_entail)))))

private def loopTryCloseInit : TacticM Unit := do
  let g ← getMainGoal
  let split? ← tryTacticCatchRuntime (withHeartbeatCap loopInitCap do
    evalTactic (← `(tactic| (
      try dsimp only
      try simp (config := { decide := true }) only [
        LoopFrame, Arm64.CalleeSavedPreserved, CalleeSavedPreserved.rfl,
        wp_norm, arm64_norm, *]
      repeat' (apply And.intro)))))
  let gs ← match split? with
    | some _ => getGoals
    | none => pure [g]
  let mut out : List MVarId := []
  for g' in gs do
    out := out ++ (← loopTryCapped g' (evalTactic (← `(tactic|
      first | done | with_reducible rfl | wp_assumption | (wp_omega_bounded; done)))))
  setGoals out

private def loopIntroIter (names : List Name) : TacticM Unit := do
  let mut ids : Array Ident := #[]
  for n in names do
    ids := ids.push (← freshIdent n)
  let hinv := ids.back!
  evalTactic (← `(tactic| intro $ids*))
  let _ ← tryTactic (evalTactic (← `(tactic| simp only [LoopFrame] at $hinv:ident ⊢)))
  wpNormAndSplitHyp hinv

private def loopDrive (applyStx : TSyntax `tactic) (hasEnt : Bool)
    (iters : List (Name × List Name)) : TacticM Unit := do
  if proofLib.wpBranchAutoDecide.get (← getOptions) then
    let pcIte? ← withoutModifyingState do
      tryTacticCatchRuntime do
        let (_, _, pcExpr) ← getSepWPStateAndPC
        if pcExpr.isAppOfArity ``ite 5 then Pure.pure (some pcExpr) else Pure.pure none
    if let some (some pcExpr) := pcIte? then
      let _ ← tryTacticCatchRuntime (resolveTerminalPcIte "loop tactic" pcExpr)
  evalTactic applyStx
  let gs ← getGoals
  let nFixed := (if hasEnt then 4 else 3)
  unless gs.length ≥ nFixed + iters.length do
    throwError "loop tactic: unexpected subgoals after applying the combinator"
  let fixed := gs.take nFixed
  let iterGoals := (gs.drop nFixed).take iters.length
  let rest := gs.drop (nFixed + iters.length)
  let gpc := fixed[0]!
  let grun := fixed[1]!
  let _ ← loopRunOn gpc loopCloseHeader
  let pcTy ← instantiateMVars (← gpc.getType)
  if let some (_, _, headPc) := pcTy.eq? then
    if let some iteSub := headPc.find? (fun e => e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) then
      let branchDetails ← gpc.withContext do
        try
          let args := iteSub.getAppArgs
          let condStr ← ppExprTruncated args[1]! 120 10
          let thenStr ← formatShortHexAddr args[3]!
          let elseStr ← formatShortHexAddr args[4]!
          Pure.pure m!"\n  condition: {condStr}\n  then PC:   {thenStr}\n  else PC:   {elseStr}"
        catch _ =>
          Pure.pure m!"{indentExpr headPc}"
      throwError "loop tactic: the current PC is an unresolved conditional branch, so the loop \
        header cannot be determined:{branchDetails}\n\
        hint: `wp_step` / `wp_steps` already stepped the loop header's entry branch (`cbz` / `b.cond`), \
        so `wp_loop_measure` / `wp_loop_list` / `wp_nested_loop` must be called at `head_pc` before \
        stepping the header branch; otherwise, if both branches are reachable, split with `wp_if hcond` \
        (or `wp_if_join <join_pc> <inv>`), or if only one branch is feasible, prove \
        `have hcond : <cond> = true := by bv_omega` (or `= false`) before `wp_steps` / `wp_sym_steps` \
        (or simplify the current PC with `wp_simp_pre [hcond]`)"
  let _ ← loopRunOn grun loopCloseHeader
  let entGoals ← if hasEnt then loopRunOn fixed[2]! loopTryCloseEnt else pure []
  let initGoals ← loopRunOn fixed[nFixed - 1]! loopTryCloseInit
  for g in entGoals ++ initGoals do
    g.setTag `init
  let mut out : List MVarId := entGoals ++ initGoals
  for (g, (tag, names)) in iterGoals.zip iters do
    let gs' ← loopRunOn g (loopIntroIter names)
    for g' in gs' do
      g'.setTag tag
    out := out ++ gs'
  setGoals (out ++ rest)

/-- Measure-indexed loop at the current loop header (`SepWP.loop_measure` /
    `SepWP.loop_measure_sep`, or the `LoopFrame`-threading `SepWP.loop_measure_framed` with
    `frame`):
    - `wp_loop_measure m Inv`: initial measure `m : Nat`, invariant `Inv : Nat → State → Prop`,
      fixed spatial context.
    - `wp_loop_measure m Inv P_inv`: spatial invariant `P_inv : Nat → State → SepProp`.
    - `wp_loop_measure frame m Inv [P_inv]`: also thread `LoopFrame s st` (sp, lr, callee-saved).

    Leaves goals `init` (unsolved initial invariant conjuncts), `base` (measure `0`, binders
    `st hpc_st hrun_st`) and `step` (measure `m' + 1`, binders `m' st hpc_st hrun_st`; prove
    `exit ∨ back-edge`). -/
syntax "wp_loop_measure" (&" frame")? ppSpace colGt term:max ppSpace colGt term:max
  (ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wp_loop_measure $[frame%$fr]? $m:term $inv:term $[$pinv?:term]?) => do
    let framed := fr.isSome
    let applyStx ← match framed, pinv? with
      | false, none => `(tactic| apply SepWP.loop_measure (m := $m) $inv)
      | false, some p => `(tactic| apply SepWP.loop_measure_sep (m := $m) $p $inv)
      | true, none => `(tactic| apply SepWP.loop_measure_framed_simple (m := $m) $inv)
      | true, some p => `(tactic| apply SepWP.loop_measure_framed (m := $m) $p $inv)
    loopDrive applyStx pinv?.isSome
      [(`base, [`st, `hpc_st, `hrun_st, `hinv_st]),
       (`step, [`m', `st, `hpc_st, `hrun_st, `hinv_st])]

/-- List-cursor loop at the current loop header (`SepWP.loop_list` / `SepWP.loop_list_sep`, or
    `SepWP.loop_list_framed` with `frame`):
    - `wp_loop_list xs Inv [P_inv]` with `Inv : List α → State → Prop` and optional
      `P_inv : List α → State → SepProp`.

    Leaves goals `init`, `nil` (binders `st hpc_st hrun_st`) and `cons` (binders
    `x rest st hpc_st hrun_st`; prove `exit ∨ back-edge`). -/
syntax "wp_loop_list" (&" frame")? ppSpace colGt term:max ppSpace colGt term:max
  (ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wp_loop_list $[frame%$fr]? $xs:term $inv:term $[$pinv?:term]?) => do
    let framed := fr.isSome
    let applyStx ← match framed, pinv? with
      | false, none => `(tactic| apply SepWP.loop_list (xs := $xs) $inv)
      | false, some p => `(tactic| apply SepWP.loop_list_sep (xs := $xs) $p $inv)
      | true, none => `(tactic| apply SepWP.loop_list_framed_simple (xs := $xs) $inv)
      | true, some p => `(tactic| apply SepWP.loop_list_framed (xs := $xs) $p $inv)
    loopDrive applyStx pinv?.isSome
      [(`nil, [`st, `hpc_st, `hrun_st, `hinv_st]),
       (`cons, [`x, `rest, `st, `hpc_st, `hrun_st, `hinv_st])]

/-- Nested loop at the current outer loop header (`SepWP.nested_loop_simple` /
    `SepWP.nested_loop`):
    `wp_nested_loop m inner_pc inner_exit_pc Inv_outer Inv_inner Inv_inner_exit
    [P_outer P_inner P_inner_exit]`.

    Leaves goals `init`, `done` (outer measure `0`), `enter` (outer measure `k + 1`: exit, skip the
    inner loop, or enter it at `inner_pc`), `inner` (from `inner_pc` to `inner_exit_pc`, usually
    closed with a nested `wp_loop_measure`) and `latch` (from `inner_exit_pc` back to the outer
    header). -/
syntax "wp_nested_loop" ppSpace colGt term:max ppSpace colGt term:max ppSpace colGt term:max
  ppSpace colGt term:max ppSpace colGt term:max ppSpace colGt term:max
  (ppSpace colGt term:max ppSpace colGt term:max ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wp_nested_loop $m:term $ipc:term $iepc:term $io:term $ii:term $iie:term
      $[$po:term $pi:term $pie:term]?) => do
    let hasSep := po.isSome
    let applyStx ← match po, pi, pie with
      | some po, some pi, some pie =>
        `(tactic| apply SepWP.nested_loop (m := $m) (inner_pc := $ipc) (inner_exit_pc := $iepc)
            $po $pi $pie $io $ii $iie)
      | _, _, _ =>
        `(tactic| apply SepWP.nested_loop_simple (m := $m) (inner_pc := $ipc)
            (inner_exit_pc := $iepc) $io $ii $iie)
    loopDrive applyStx hasSep
      [(`done, [`st, `hpc_st, `hrun_st, `hinv_st]),
       (`enter, [`k, `st, `hpc_st, `hrun_st, `hinv_st]),
       (`inner, [`k, `st, `hpc_st, `hrun_st, `hinv_st]),
       (`latch, [`k, `st, `hpc_st, `hrun_st, `hinv_st])]

end

end ProofLib
