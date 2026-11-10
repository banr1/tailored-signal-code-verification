/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# ARM64 Deterministic Simulator

Executable single-step and bounded multi-step evaluators (`stepState`, `execN`, `execUntilPC`,
`stepInst`) and flat test-memory helpers (`Program.loadCode`, `Memory.mapRestRw`). Contains no
theorems so test executables can link it without proof terms; soundness is proved in
`ProofLib.Simulation`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Deterministic single-step evaluator for a `Program` and `State`. Hooks are applied without
    checking `Memory.KeepsFrozen`; see `Program.HooksKeepFrozen`. -/
def stepState (prog : Program) (s : State) : Option State :=
  match s.status with
  | .Running =>
    match prog.externAt? s.pc with
    | some f => some (f s)
    | none =>
      match prog.fetchMem s.mem s.pc with
      | some inst => some (prog.evalInst inst s)
      | none      => some { s with status := .Halted }
  | _ => none

/-- Execute up to `n` steps of `prog` from state `s`. -/
def execN (n : Nat) (prog : Program) (s : State) : State :=
  match n with
  | 0 => s
  | n + 1 =>
    match stepState prog s with
    | some s' => execN n prog s'
    | none    => s

/-- Execute up to `n` steps of `prog` from state `s`, stopping immediately once `s.pc == target_pc`
    or `s.status != .Running`. -/
def execUntilPC (n : Nat) (prog : Program) (target_pc : BitVec 64) (s : State) : State :=
  match n with
  | 0 => s
  | n + 1 =>
    if s.pc == target_pc || s.status != .Running then
      s
    else
      match stepState prog s with
      | some s' => execUntilPC n prog target_pc s'
      | none    => s

/-- `m` with `prog.code` mapped read-execute at `prog.base`, leaving all other bytes unchanged. -/
def _root_.Arm64.Program.loadCode (prog : Program) (m : Memory) : Memory :=
  let code := prog.code.toArray
  Memory.ofFn
    (fun a =>
      let i := (a - prog.base).toNat
      if i < code.size then code[i]! else m.read8 a)
    (fun a => if (a - prog.base).toNat < code.size then some Perm.rx else m.perm a)

/-- `m` with every unmapped byte mapped read-write (a flat test memory). -/
def _root_.Arm64.Memory.mapRestRw (m : Memory) : Memory := m.mapFresh 0 (2 ^ 64) Perm.rw

/-- Compute the next state by fetching and executing the instruction at `s.pc`. -/
def stepInst (prog : Program) (s : State) : State :=
  match prog.fetch s.pc with
  | some inst => prog.evalInst inst s
  | none      => { s with status := .Halted }

end ProofLib
