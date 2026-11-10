/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
import Arm64.Trusted.Spec.SepLogic

/-!
# Proof-Engineering Profiling Helpers

Tactic and command timing utilities (`timed`, `#proof_stats`, and `#timed_decl`) for logging
elaboration wall-clock time, heartbeats, proof-term DAG/tree size, and kernel type-checking time.
-/

public meta section

namespace ProofLib.Profile

open Lean Meta Elab Tactic Command

/-- `timed "label" tac`: run `tac`, log wall-clock ms and heartbeats (in thousands). -/
syntax (name := timedTac) "timed " str ppSpace tacticSeq : tactic

@[tactic timedTac] def evalTimed : Tactic := fun stx => do
  let label := stx[1].isStrLit?.getD ""
  let t0 ← IO.monoNanosNow
  let h0 ← IO.getNumHeartbeats
  evalTactic stx[2]
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  logInfo m!"timed {label}: {(t1 - t0) / 1000000} ms, {(h1 - h0) / 1000} kHB"

/-- Unshared tree size of `e`, stopping at `cap`. -/
partial def treeSize (e : Expr) (cap : Nat) : Nat :=
  go e 0
where
  go (e : Expr) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match e with
    | .app f a => go a (go f (acc + 1))
    | .lam _ t b _ | .forallE _ t b _ => go b (go t (acc + 1))
    | .letE _ t v b _ => go b (go v (go t (acc + 1)))
    | .mdata _ b => go b (acc + 1)
    | .proj _ _ b => go b (acc + 1)
    | _ => acc + 1

/-- Log the proof-term size of theorem `n` and the time the kernel takes to re-check it. -/
def logProofStats (n : Name) : CommandElabM Unit := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  let some v := ci.value? (allowOpaque := true) | throwError "{n} has no value"
  let dag ← v.numObjs
  let tree := treeSize v 100000000
  let decl : Declaration := .thmDecl
    { name := n ++ `_proof_stats_recheck, levelParams := ci.levelParams, type := ci.type, value := v }
  let t0 ← IO.monoNanosNow
  let env ← getEnv
  let maxRec := (maxRecDepth.get (← getOptions)).toUSize
  let ok ← IO.lazyPure fun _ =>
    match env.addDeclCore 0 maxRec decl none with | .ok _ => "ok" | .error _ => "FAILED"
  let t1 ← IO.monoNanosNow
  logInfo m!"proof_stats {n}: dag objects {dag}, tree size {tree}, kernel re-check {(t1 - t0) / 1000} µs ({ok})"

/-- `#proof_stats c`: proof-term size and kernel re-check time of constant `c`. -/
elab "#proof_stats " id:ident : command => do
  logProofStats (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id)

/-- `#timed_decl cmd`: elaborate the declaration command `cmd` synchronously (`Elab.async false`)
    and, for every non-internal theorem it adds, log the command's wall-clock time and heartbeats
    (`timed <name>: ... ms, ... kHB`, covering tactic elaboration and the kernel check) followed by
    `#proof_stats`. -/
elab "#timed_decl " cmd:command : command => do
  let before := (← getEnv).constants.map₂.foldl (fun s n _ => s.insert n) ({} : NameSet)
  let t0 ← IO.monoNanosNow
  let h0 ← IO.getNumHeartbeats
  withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) (elabCommand cmd)
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  let env ← getEnv
  -- Equation lemmas (`f.eq_1`, `f.eq_def`) of definitions unfolded by the proof are realized
  -- on demand during elaboration; they are reserved names, not theorems of this command.
  let added := env.constants.map₂.foldl (fun acc n ci =>
    if !before.contains n && !n.isInternal && !isReservedName env n && ci matches .thmInfo _
    then acc.push n else acc) #[]
  for n in added.qsort (·.toString < ·.toString) do
    logInfo m!"timed {n}: {(t1 - t0) / 1000000} ms, {(h1 - h0) / 1000} kHB"
    logProofStats n

end ProofLib.Profile
