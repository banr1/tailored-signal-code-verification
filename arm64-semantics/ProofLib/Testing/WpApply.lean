/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.Apply
public import ProofLib.SepLogic.Tests

/-!
# Contract Lookup Regression Tests

Tests `@[wp_spec]`, `wp_apply`, `wp_apply?`, `wp_spec_intro`, and custom `frame` procedures on
local hypotheses, registered lemmas, and `∀`-quantified entry-relative contracts, along with
negative `#guard_msgs` error cases.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpApply

open Arm64 _root_.ProofLib _root_.ProofLib.SepLogic.Tests

/-! ## Local hypothesis lookup -/

/-- `bump_pair_ok` with both `wp_call h_bump` replaced by `wp_apply`. -/
theorem bump_pair_ok_apply (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellSpec) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_done

/-! ## Global `@[wp_spec]` lookup, `using`, and `wp_apply?` -/

/-- Callee facts bundled in a structure, so they are not themselves contract candidates. -/
structure BumpCallee (prog : Program) : Prop where
  addr : prog.fnAddr "bump_cell" = bump_cell_addr
  ok : prog.subroutineOk "bump_cell" bumpCellSpec

/-- The callee contract as a lemma whose hypothesis the caller has in context. -/
theorem bump_cell_contract {prog : Program} (hC : BumpCallee prog) :
    subroutine_ok prog bump_cell_addr bumpCellSpec := by
  have h := hC.ok
  simp only [Program.subroutineOk, hC.addr] at h
  exact h

section Global

attribute [local wp_spec] bump_cell_contract

/-- The contract is found through the `@[wp_spec]` index (no local contract hypothesis), its
    `hC` parameter by assumption; the second call names it with `using`. -/
theorem bump_pair_ok_global (prog : Program) (h_code : BumpPairCodeAt prog)
    (hC : BumpCallee prog) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps
  wp_apply
  wp_steps
  wp_apply using bump_cell_contract hC
  wp_steps
  wp_done

end Global

/-! ## Frame-procedure hook -/

/-- The hook as a tactic (`sep_frame`, the backtracking frame solver). -/
theorem bump_pair_ok_frameTac (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellSpec) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps
  wp_apply (frame := sep_frame)
  wp_steps
  wp_apply (frame := sep_frame)
  wp_steps
  wp_done

open Lean Elab Tactic in
/-- The hook as a `SepFrameInfer.FrameProc` value, passed from Lean code. -/
elab "test_wp_apply_frameproc" : tactic => do
  WpApply.wpApplyCore { frame? := some (.proc SepFrameInfer.frameProc) } (← getRef)

theorem bump_pair_ok_frameProc (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellSpec) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps
  test_wp_apply_frameproc
  wp_steps
  test_wp_apply_frameproc
  wp_steps
  wp_done

-- A hook tactic that does not close the precondition rejects the candidate.
/--
error: wp_apply: no candidate contract applies at PC
  65536#64
h_bump: wp_apply: the frame procedure did not prove the callee precondition
-/
#guard_msgs (error, drop info) in
theorem bump_pair_bad_frame (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellSpec) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps
  wp_apply (frame := skip)

/-! ## `∀`-quantified contracts, `autoParam` parameters, and `wp_spec_intro` -/

/-- Dummy spec for an entry-relative callee contract. -/
abbrev relSpec : Spec Unit :=
  Spec.split (fun _ _ => True) (fun _ => emp) (fun _ _ sf => sf.readReg64 .x0 = 42#64) (fun _ => emp)

structure RelCallee (prog : Program) : Prop where
  ok : subroutine_ok prog (prog.fnAddr "f" + 0x40#64) relSpec

/-- The entry-relative contract: `name` and `k` are determined by the call site. -/
theorem rel_contract {prog : Program} (hC : RelCallee prog) {name : String} {k : Nat}
    (hk : name = "f" ∧ k = 0x40 := by decide) :
    subroutine_ok prog (prog.fnAddr name + BitVec.ofNat 64 k) relSpec := by
  obtain ⟨rfl, rfl⟩ := hk
  exact hC.ok

/-- `wp_spec_intro` takes `name` from the goal's entry and keeps `k` (and its `autoParam`
    side condition) `∀`-bound. -/
theorem spec_intro_shape (prog : Program) (hC : RelCallee prog) (spec : Spec Unit)
    (hgoal : subroutine_ok prog (prog.fnAddr "f") spec) :
    subroutine_ok prog (prog.fnAddr "f") spec := by
  wp_spec_intro [rel_contract]
  have h : subroutine_ok prog (prog.fnAddr "f" + BitVec.ofNat 64 0x40) relSpec :=
    h_rel_contract (k := 0x40)
  exact hgoal

/-- At a call site after entry generalization (`entry` abstract), `wp_apply` instantiates a
    `∀`-quantified local contract: `k` by address unification, `hk` by its `autoParam` tactic. -/
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 0x40#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_rel : ∀ {k : Nat} (_hk : k = 0x40 := by decide), subroutine_ok prog (entry + BitVec.ofNat 64 k) relSpec) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_apply
  exact SepWP.done (by assumption) (by assumption) (by assumption)

-- `wp_apply?` reports the explicit `wp_call` (contract and ghost argument).
/--
info: Try this:
  [apply] wp_call (h_rel) (())
-/
#guard_msgs (info) in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 0x40#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_rel : subroutine_ok prog (entry + 0x40#64) relSpec) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_apply?
  exact SepWP.done (by assumption) (by assumption) (by assumption)

/-! ## Errors -/

/--
error: wp_apply: no contract for the current PC
  65536#64
no local `subroutine_ok` hypothesis and no `@[wp_spec]` lemma matches; add one, or use `wp_apply using h`
-/
#guard_msgs (error, drop info) in
theorem bump_pair_no_contract (prog : Program) (h_code : BumpPairCodeAt prog) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps
  wp_apply


-- Every candidate is rejected: the only local contract is for another address.
/--
error: wp_apply: no candidate contract applies at PC
  entry + 64#64
h_other: callee address
  entry + 128#64
differs from the current PC
  entry + 64#64
-/
#guard_msgs (error, drop info) in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 0x40#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_other : subroutine_ok prog (entry + 0x80#64) relSpec) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_apply

-- An `autoParam` side condition that fails rejects the candidate.
/--
error: wp_apply: no candidate contract applies at PC
  entry + 64#64
h_rel: cannot prove the contract hypothesis `_hk`:
  64 = 68
(tried local assumptions and its default tactic); pass it with `wp_apply using`
-/
#guard_msgs (error, drop info) in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 0x40#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_rel : ∀ {k : Nat} (_hk : k = 0x44 := by decide), subroutine_ok prog (entry + BitVec.ofNat 64 k) relSpec) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_apply

-- `@[wp_spec]` rejects a lemma that is not a `subroutine_ok` contract.
theorem not_a_contract : (1 : Nat) + 1 = 2 := rfl

/--
error: @[wp_spec]: the conclusion of `Examples.Testing.ProofLib.WpApply.not_a_contract` is not a `subroutine_ok prog addr spec` contract (after its binders and unfolding `Program.subroutineOk`-style wrappers)
-/
#guard_msgs in
attribute [local wp_spec] not_a_contract

end Examples.Testing.ProofLib.WpApply
