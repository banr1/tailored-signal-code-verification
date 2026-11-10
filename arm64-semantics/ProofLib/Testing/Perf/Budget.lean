/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# Heartbeat Budgets for Performance Regression Tests

Defines `#perf_budget N in cmd`, which elaborates `cmd` synchronously under `maxHeartbeats N` and
logs an error if total tactic elaboration plus kernel typechecking exceeds `N` (in units of 1000
raw heartbeats). This detects regressions where individual phases stay within internal
`withHeartbeatCap` limits yet the declaration exceeds `N` overall. Setting
`set_option perfTest.report true` logs measured heartbeat usage on passing commands as well.

Wrap negative tests in `#guard_msgs` to assert the tactic diagnostic on budget:
```lean
/-- error: wp_done: postcondition value mismatch: ... -/
#guard_msgs (error, drop info) in
#perf_budget 100000 in
example ... := by wp_init u s0; wp_steps; wp_done
```
Set `N` to roughly 2-3x the measured cost.
-/

public meta section

namespace Examples.Testing.ProofLib.Perf

open Lean Elab Command

register_option perfTest.report : Bool := {
  defValue := false
  descr := "make `#perf_budget` log the heartbeats (in `maxHeartbeats` units) each budgeted command used"
}

private def addedDeclNames (before : NameSet) : CommandElabM (Array Name) := do
  let env ← getEnv
  let added := env.constants.map₂.foldl (fun acc n _ =>
    if !before.contains n && !n.isInternal && !isReservedName env n then acc.push n else acc) #[]
  return added.qsort (·.toString < ·.toString)

/-- `#perf_budget N in cmd`: run `cmd` with `maxHeartbeats N` (synchronously, so every heartbeat
    of tactic elaboration and the kernel check is counted here) and fail if it used more than `N`
    (in `maxHeartbeats` units). -/
syntax (name := perfBudgetCmd) "#perf_budget " num " in" ppLine command : command

@[command_elab perfBudgetCmd] def elabPerfBudget : CommandElab := fun stx => do
  let budget := stx[1].isNatLit?.getD 0
  let cmd := stx[3]
  let before := (← getEnv).constants.map₂.foldl (fun s n _ => s.insert n) ({} : NameSet)
  let h0 ← IO.getNumHeartbeats
  withScope (fun sc => { sc with opts := maxHeartbeats.set (Elab.async.set sc.opts false) budget })
    (elabCommand cmd)
  let used := (← IO.getNumHeartbeats) - h0
  let usedK := used / 1000
  let names ← addedDeclNames before
  let label := if names.isEmpty then m!"command" else m!"{names.toList}"
  if used > budget * 1000 then
    logErrorAt cmd m!"perf_budget: {label} used {usedK} heartbeats, over its budget of {budget}; \
      find the regression (`set_option perfTest.report true` / `timed`) or, if the extra cost is \
      intended, raise the budget to about 2–3× the new cost"
  else if perfTest.report.get (← getOptions) then
    logInfoAt cmd m!"perf_budget: {label} used {usedK} heartbeats (budget {budget})"

end Examples.Testing.ProofLib.Perf
