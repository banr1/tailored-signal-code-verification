/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.SepLogic.BlockSummary
public import ProofLib.SepLogic.SymBlock.Tactic

/-!
# `block_summary` and `wp_block` Regression Tests

Tests `block_summary` across the default `wp_step`, `wp_sym_steps`, and `sym_block` engines, reuse
of a generic segment summary across multiple postconditions, code addresses, and framed
preconditions via `wp_block`, and negative diagnostics for malformed or failing summaries.
-/

@[expose] public section

namespace Testing.BlockSummary

open Arm64 ProofLib

arm64_proof_prelude

/-- Position-independent 4-instruction segment: `x5 := [x0 + 8] + 2; [x0 + 8] := x5`:
    `ldr x5, [x0, #8]; add x5, x5, #1; add x5, x5, #1; str x5, [x0, #8]`. -/
def segWords : List (BitVec 32) := "f9400405 910004a5 910004a5 f9000405"

/-- The segment, summarized once with the default `wp_step` engine. -/
block_summary seg_ok {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 16#64)

/--
info: Testing.BlockSummary.seg_ok {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords) {s : State}
  {p v : BitVec 64} {F : SepProp} (hpc : s.pc = base) (hrun : s.status = ExecStatus.Running)
  (hx0 : s.readReg64 Reg.x0 = p) {target : BitVec 64} {post : State → SepProp → Prop} {oom : State → SepProp}
  (hnext :
    ∀ (m : Memory),
      SepWP prog target (((s.writeReg64 (Reg.gpr 5#5) (v + 2#64)).setPC (base + 16#64)).setMem m)
        ((p + 8#64) ↦₆₄ (v + 2#64) ∗ F) post oom) :
  SepWP prog target s ((p + 8#64) ↦₆₄ v ∗ F) post oom
-/
#guard_msgs in
#check seg_ok

/-- info: 'Testing.BlockSummary.seg_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seg_ok

/-- The same summary built by the `SymM` engine and by the reflective block engine. -/
block_summary seg_sym {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 16#64) using wp_sym_steps 4

block_summary seg_blk {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 16#64) using sym_block 4

set_option proofLib.blockSummary.maxSteps 4 in
/-- A segment of exactly `maxSteps` instructions is accepted (the bound is inclusive). -/
block_summary seg_bound {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 16#64)

/--
error: block_summary: no state with pc = base + 16#64 within 3 instructions (set_option proofLib.blockSummary.maxSteps)
-/
#guard_msgs in
set_option proofLib.blockSummary.maxSteps 3 in
block_summary seg_short {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 16#64)

-- All three engines produce the same statement.
example : type_of% @seg_sym = type_of% @seg_ok := rfl
example : type_of% @seg_blk = type_of% @seg_ok := rfl

/-! ## Reuse under two postconditions (spec variants) -/

/-- Variant A: exact final context and the loaded value. -/
theorem variantA {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 16#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 2#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 2#64) := by
  wp_block seg_ok
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

/-- Variant B: entailment-shaped final context and a preserved register. -/
theorem variantB {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 16#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => (Pf ⊢ ((p + 8#64) ↦₆₄ (v + 2#64)) ∗ F) ∧ sf.readReg64 .x0 = p) := by
  wp_block seg_ok
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨Entails.refl _, by simp only [wp_norm, arm64_norm, hx0]⟩

/-- The same as `variantA`, stepped by hand (baseline). -/
theorem variantA_hand {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 16#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 2#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 2#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

/-! ## The same code at two addresses, inside a larger precondition -/

/-- Two copies of the segment back to back: the second application names the code base, which the
    goal does not determine by itself; the extra atom `q ↦₆₄ w` is framed by `sep_frame`. -/
theorem twice {prog : Program} {base : BitVec 64} (h1 : prog.hasCode base segWords)
    (h2 : prog.hasCode (base + 16#64) segWords)
    {s : State} {p q v w : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 32#64) s ((q ↦₆₄ w) ∗ ((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => (Pf ⊢ ((p + 8#64) ↦₆₄ (v + 4#64)) ∗ (q ↦₆₄ w) ∗ F) ∧
        sf.readReg64 .x5 = v + 4#64) := by
  wp_block seg_ok
  wp_block seg_ok (base := base + 16#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, by simp only [wp_norm, arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  sep_frame

/-- info: 'Testing.BlockSummary.twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twice

/-- When the caller precondition contains multiple identically shaped points-to cells
    `((p1 + 8#64) ↦₆₄ v1) ∗ ((p2 + 8#64) ↦₆₄ v2) ∗ F`, `wp_block` discharges register side
    conditions (`hx0 : s.readReg64 .x0 = p2`) before running `sep_frame`, so `sep_frame` matches
    the cell at `p2 + 8#64` instead of greedily unifying `?p` against `p1`, and updates it in
    place inside the caller's precondition. -/
theorem multi_cell_frame {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p1 p2 v1 v2 : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p2) :
    SepWP prog (base + 16#64) s (((p1 + 8#64) ↦₆₄ v1) ∗ ((p2 + 8#64) ↦₆₄ v2) ∗ F)
      (fun sf Pf => (Pf ⊢ ((p1 + 8#64) ↦₆₄ v1) ∗ ((p2 + 8#64) ↦₆₄ (v2 + 2#64)) ∗ F) ∧
        sf.readReg64 .x5 = v2 + 2#64) := by
  wp_block seg_ok
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨Entails.refl _, by simp only [wp_norm, arm64_norm]⟩

/-! ## Negative tests -/

/--
error: block_summary: could not step at pc base + 16#64 (after 4 instructions) before reaching base + 6#64:
  wp_step: could not fetch/decode instruction at PC `base + 16#64`
  hint: check (1) the `*Fns.lean` / `*Code.lean` decode module is imported or a `hasWords` / `hasCode` / `code_fetches` hypothesis is in context, (2) the PC offset is normalized (e.g. `entry + <off>#64`; try `wp_simp_pre` or `examples_generalize_entry`), or (3) execution did not step past function exit or into an un-inlined `BL` callee
-/
#guard_msgs (whitespace := lax) in
block_summary bad_stop {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 6#64)

/--
error: block_summary: the run stopped at pc
  base + 8#64
not at
  base + 16#64
-/
#guard_msgs in
block_summary bad_using {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 16#64) using wp_sym_steps 2

/--
error: block_summary: expected a statement `BlockSegment prog s P stop`, got
  True
-/
#guard_msgs in
block_summary bad_shape {prog : Program} : True

/-- error: block_summary: 'Testing.BlockSummary.seg_ok' has already been declared -/
#guard_msgs in
block_summary seg_ok {prog : Program} {s : State} {P : SepProp} : BlockSegment prog s P 0#64

/--
error: wp_block: the goal's precondition does not contain the summary's precondition (sep_frame failed):
  sep_frame: no hypothesis atom matches goal atom
    (p + 8#64) ↦₆₄ ?v
  unmatched hypothesis atoms: p ↦₆₄ v, F
-/
#guard_msgs (whitespace := lax) in
example {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base segWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 16#64) s ((p ↦₆₄ v) ∗ F) (fun _ _ => True) := by
  wp_block seg_ok

/--
error: wp_block: goal is not a `SepWP` judgement:
  True
-/
#guard_msgs in
example : True := by
  wp_block seg_ok

end Testing.BlockSummary
