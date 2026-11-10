/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.ObjectLoad
public import ProofLib.GenDecodes
public import ProofLib.Hoare.OracleHook

/-!
# Regression Tests for `ProofLib.Hoare.OracleHook`

Exercises oracle-valued external symbol hooks (`OracleExterns`, `FreeOracle`, `RunsToAt`, `RunsTo`,
`oracle_step`, and `simulateQ_execUntilPCWithOracle`) on a toy AArch64 program that increments `x0`,
calls an oracle-hooked `hash_word` stub via `BL`, and branches to the exit address.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.OracleHook

open Arm64
open _root_.ProofLib
open _root_.ProofLib.ProgramReflection
open _root_.ProofLib.GenDecodes

/-
Memory layout (base `0#64`, exit target `0x10`):
- `caller` (offset `0x00`):
    0x00: add x0, x0, #1   (0x91000400)
    0x04: bl 0x0c          (0x94000002)
    0x08: b 0x10           (0x14000002)
- `hash_word` (offset `0x0c`):
    0x0c: udf #0           (0x00000000) -- replaced by oracle hook
-/
def oracleToyProg_tree : WordTree :=
  .node 2
    (.node 1
      (.leaf 0x00#8 0x04#8 0x00#8 0x91#8)  -- 0x00: add x0, x0, #1
      (.leaf 0x02#8 0x00#8 0x00#8 0x94#8)) -- 0x04: bl +8 (target 0x0c)
    (.node 1
      (.leaf 0x02#8 0x00#8 0x00#8 0x14#8)  -- 0x08: b +8 (target 0x10)
      (.leaf 0x00#8 0x00#8 0x00#8 0x00#8)) -- 0x0c: udf #0

def oracleToyProg : Program :=
  { base := 0#64
    code := oracleToyProg_tree.toBytes
    symbols := [
      ("caller",    0x00),
      ("hash_word", 0x0c)
    ]
    stubs := [] }

theorem oracleToyProg_fetch_at (off : Nat) (inst : Instr)
    (h : oracleToyProg_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64) :
    oracleToyProg.fetch (BitVec.ofNat 64 off) = some inst := by
  simpa [oracleToyProg] using
    fetch_of_wordTree (prog := oracleToyProg) (t := oracleToyProg_tree) 4 rfl rfl h hoff
      (hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) off)

theorem oracleToyProg_fetch_rebase_text (b : BitVec 64) (X : String → Option (State → State))
    (off : Nat) (inst : Instr) (h : oracleToyProg_tree.fetchDecodeAt off = some inst)
    (htext : off < 12) (hoff : off < 2 ^ 64) :
    (oracleToyProg.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :=
  (Program.fetch_rebase_of_noStubBefore (P := oracleToyProg) rfl (fun _ => rfl) (fun _ => rfl)
    rfl b X htext hoff).trans (oracleToyProg_fetch_at off inst h hoff)

gen_fetches oracleToyProg oracleToy 12 true [0x0 → 0x8]

/-! ## Oracle Family and Hook Table -/

/-- Single-query oracle family mapping a 64-bit word to a 64-bit digest. -/
def wordHashOracle : OracleFamily Unit :=
  fun _ => (BitVec 64, BitVec 64)

/-- Oracle-valued hook for `"hash_word"`: queries `wordHashOracle` on `x0`, writes the digest to
    `x0`, and returns to `lr` (`x30`). -/
def hashWordHook (s : State) : FreeOracle wordHashOracle State := do
  let digest ← FreeOracle.query () (s.readReg64 .x0)
  pure ((s.writeReg64 .x0 digest).setPC (s.readReg64 .lr))

/-- Oracle hook table attaching `hashWordHook` to `"hash_word"`. -/
def hashHooks : OracleExterns (FreeOracle wordHashOracle) :=
  fun sym => if sym == "hash_word" then some hashWordHook else none

theorem oracleToyProg_no_overrides (sym : String) :
    oracleToyProg.overrides sym = none := rfl

theorem oracleToyProg_hooksKeepFrozen :
    oracleToyProg.HooksKeepFrozen := by
  intro pc f s hf
  unfold Program.externAt? Program.hookAtOff? oracleToyProg at hf
  simp [List.findSome?] at hf

theorem hashHooks_keepFrozen : hashHooks.KeepFrozen := by
  intro impl sym f s hf
  unfold OracleExterns.withHandler hashHooks at hf
  by_cases hsym : (sym == "hash_word") = true
  · rw [hsym] at hf
    simp only [↓reduceIte, Option.map_some, Option.some.injEq] at hf
    subst hf
    exact ⟨Memory.KeepsFrozen.refl _, rfl⟩
  · rw [Bool.eq_false_of_ne_true hsym] at hf
    exact nomatch hf

theorem oracleToyProg_withHandler_hooksKeepFrozen
    (impl : FreeOracle.Handler wordHashOracle) :
    ({ oracleToyProg with overrides := hashHooks.withHandler impl } : Program).HooksKeepFrozen :=
  hashHooks_keepFrozen.hooksKeepFrozen oracleToyProg_no_overrides
    oracleToyProg_hooksKeepFrozen impl

@[simp, arm64_norm]
theorem oracleToyProg_oracleExternAt_0 :
    oracleToyProg.oracleExternAt? hashHooks 0#64 = none :=
  Program.oracleHookAtOff?_eq_none (hookedOffs := [0x0c]) rfl rfl

@[simp, arm64_norm]
theorem oracleToyProg_oracleExternAt_4 :
    oracleToyProg.oracleExternAt? hashHooks 4#64 = none :=
  Program.oracleHookAtOff?_eq_none (hookedOffs := [0x0c]) rfl rfl

@[simp, arm64_norm]
theorem oracleToyProg_oracleExternAt_8 :
    oracleToyProg.oracleExternAt? hashHooks 8#64 = none :=
  Program.oracleHookAtOff?_eq_none (hookedOffs := [0x0c]) rfl rfl

@[simp, arm64_norm]
theorem oracleToyProg_oracleExternAt_c :
    oracleToyProg.oracleExternAt? hashHooks 12#64 = some hashWordHook := rfl

/-! ## Counted Run and Pure Handler Adequacy -/

/-- Step `caller` through `0x00` (`add x0, x0, #1`) and `0x04` (`bl 0x0c`) to the oracle-hooked
    entry `0x0c` using `oracle_step`. -/
theorem caller_pre_hook_runsToAt (s0 : State)
    (hpc : s0.pc = 0#64) (hrun : s0.status = .Running) :
    RunsToAt oracleToyProg hashHooks 16#64 2 s0
      (fun s1 =>
        s1.pc = 12#64 ∧
        s1.status = .Running ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 + 1#64 ∧
        s1.readReg64 .lr = 8#64) := by
  oracle_step
  oracle_step
  apply RunsToAt.refl
  simp only [arm64_norm, hrun, and_self]

/-- Step from `0x08` (`b 0x10`) to the target `0x10` in 1 instruction step. -/
theorem caller_post_hook_runsTo (s2 : State) (digest : BitVec 64)
    (hpc2 : s2.pc = 8#64) (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 .x0 = digest) :
    RunsTo oracleToyProg hashHooks 16#64 1 s2
      (fun sf => pure (sf.readReg64 .x0))
      (pure digest) := by
  have hstep : RunsToAt oracleToyProg hashHooks 16#64 1 s2
      (fun sf => sf.pc = 16#64 ∧ sf.readReg64 .x0 = digest) := by
    oracle_step
    apply RunsToAt.refl
    simp only [arm64_norm, hx0_2, and_self]
  refine RunsToAt.seq (m := 0) (n := 1) hstep ?_
  intro sf ⟨hpc_f, hx0_f⟩
  exact RunsTo.done hpc_f (by rw [hx0_f])

/-- Full counted oracle run of `caller`: 2 instruction steps (`add`, `bl`), 1 oracle hook step at
    `0x0c` (`hashWordHook`), and 1 instruction step at `0x08` (`b 0x10`), taking 4 steps total. -/
theorem caller_runsTo (s0 : State)
    (hpc : s0.pc = 0#64) (hrun : s0.status = .Running) :
    RunsTo oracleToyProg hashHooks 16#64 4 s0
      (fun sf => pure (sf.readReg64 .x0))
      (FreeOracle.query () (s0.readReg64 .x0 + 1#64)) := by
  have hpre := caller_pre_hook_runsToAt s0 hpc hrun
  refine RunsToAt.seq (m := 2) (n := 2) hpre ?_
  intro s1 ⟨hpc1, hrun1, hx0_1, hlr_1⟩
  have hne12 : s1.pc ≠ 16#64 := by rw [hpc1]; decide
  have hhook_c : oracleToyProg.oracleExternAt? hashHooks s1.pc = some hashWordHook := by
    rw [hpc1]; exact oracleToyProg_oracleExternAt_c
  apply RunsTo.hook (n := 1) hne12 hrun1 hhook_c
  intro hL1 j
  unfold hashWordHook
  rw [hx0_1, hlr_1, bind_assoc]
  refine Eq.trans ?_ (bind_pure (FreeOracle.query (spec := wordHashOracle) () (s0.readReg64 .x0 + 1#64)))
  congr 1
  funext digest
  rw [pure_bind]
  exact caller_post_hook_runsTo ((s1.writeReg64 .x0 digest).setPC 8#64) digest
    rfl hrun1 rfl hL1 j

/-- End-to-end pure handler adequacy via `RunsTo.exec` and `simulateQ_execUntilPCWithOracle`:
    for any pure handler `impl` and any `fuel ≥ 4`, running `execUntilPC` on the pure-hooked
    program yields `x0 = impl () (s0.readReg64 .x0 + 1#64)`. -/
theorem caller_execUntilPC_withHandler (impl : FreeOracle.Handler wordHashOracle)
    (s0 : State) (hpc : s0.pc = 0#64) (hrun : s0.status = .Running)
    (hL : oracleToyProg.CodeLoaded s0.mem) (fuel : Nat) (hle : 4 ≤ fuel) :
    (execUntilPC fuel { oracleToyProg with overrides := hashHooks.withHandler impl } 16#64 s0).readReg64 .x0 =
      impl () (s0.readReg64 .x0 + 1#64) := by
  have hexec := (caller_runsTo s0 hpc hrun).exec hL fuel hle
  have hsim := FreeOracle.simulate_bind impl
    (execUntilPCWithOracle fuel oracleToyProg hashHooks 16#64 s0)
    (fun sf => pure (sf.readReg64 .x0))
  rw [hexec] at hsim
  have hbridge := simulateQ_execUntilPCWithOracle impl oracleToyProg hashHooks
    oracleToyProg_no_overrides fuel 16#64 s0
  change FreeOracle.simulate impl (execUntilPCWithOracle fuel oracleToyProg hashHooks 16#64 s0) = _ at hbridge
  rw [hbridge] at hsim
  exact hsim.symm

/--
info: 'Examples.Testing.ProofLib.OracleHook.caller_runsTo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller_runsTo

/--
info: 'Examples.Testing.ProofLib.OracleHook.caller_execUntilPC_withHandler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms caller_execUntilPC_withHandler

end Examples.Testing.ProofLib.OracleHook

end
