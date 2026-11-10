/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.Syscalls
public import ProofLib.SepLogic.WPp
public import ProofLib.SepLogic.WPFrozen
public import ProofLib.SepLogic.Basic
public import ProofLib.VCGen
public import ProofLib.Abi.Aapcs
public import ProofLib.Abi.Rust

/-!
# Separation-Logic Automation Tests

Regression and unit tests for separation-logic entailment (`sep_entail`, `sep_focus`, `sep_facts`),
store stepping (`arm64_sep_close`), and `SepWP` / `SepWPp` program-verification tactics.
-/

@[expose] public section

namespace ProofLib.SepLogic.Tests

open Arm64 ProofLib

variable (m : Memory) (a b c : BitVec 64) (x y z : BitVec 64) (R F : SepProp)

/-! ## Reflective AC Normalization (`sep_entail`) -/

example (h : m ⊨ (a ↦₆₄ x) ∗ ((b ↦₆₄ y) ∗ R)) : m ⊨ (R ∗ (b ↦₆₄ y)) ∗ (a ↦₆₄ x) := by
  sep_entail

example (h : m ⊨ ((a ↦₆₄ x) ∗ emp) ∗ (emp ∗ R)) : m ⊨ R ∗ (a ↦₆₄ x) := by
  sep_entail

example (_h : m ⊨ emp) : m ⊨ emp := by
  sep_entail

/-- Duplicated atoms are counted with multiplicity. -/
example (h : m ⊨ R ∗ R ∗ F) : m ⊨ F ∗ (R ∗ R) := by
  sep_entail

/-! ## Affine Hypothesis Dropping -/

example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₈ 3#8) ∗ (c ↦₃₂ 9#32) ∗ R) : m ⊨ R ∗ (a ↦₆₄ x) := by
  sep_entail

/-! ## Cancellation with Value Side Goals and Retyping -/

example (hxy : x = y) (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ R ∗ (a ↦₆₄ y) := by
  sep_entail

example (h : m ⊨ (a ↦₆₄ (x + 0#64)) ∗ R) : m ⊨ R ∗ (a ↦₆₄ x) := by
  sep_entail

example (v : BitVec 16) (h : m ⊨ (a ↦₁₆ (v ^^^ 0#16)) ∗ R) : m ⊨ R ∗ (a ↦₁₆ v) := by
  sep_entail

example (v : BitVec 32) (h : m ⊨ (a ↦₃₂ (v + 1#32 - 1#32)) ∗ R) : m ⊨ (a ↦₃₂ v) ∗ R := by
  sep_entail

/-- Same base address up to reducible unfolding (`stackFrame16` / `stackFrame32` abbreviations). -/
example (s : State) (h : m ⊨ stackFrame16At s.sp ∗ R) : m ⊨ R ∗ stackFrame16 s := by
  sep_entail

example (s : State) (h : m ⊨ stackFrame32 s ∗ R) : m ⊨ R ∗ stackFrame32At s.sp := by
  sep_entail

/-- Retyping an untyped region: the new value is read out of memory. -/
example (hv : m.read64 a = x) (h : m ⊨ memRegion a 8 ∗ R) : m ⊨ (a ↦₆₄ x) ∗ R := by
  sep_entail

/-- A typed prefix of a larger region. -/
example (hv : m.read64 a = x) (h : m ⊨ memRegion a 32 ∗ R) : m ⊨ (a ↦₆₄ x) ∗ R := by
  sep_entail

/-- Forgetting contents of fixed-width and compound blocks into `memRegion`. -/
example (h : m ⊨ (a ↦₁₂₈ 5#128) ∗ R) : m ⊨ memRegion a 16 ∗ R := by
  sep_entail

/-! ## Frame Inference, Ghost Instantiation, and Pure/Existential Atoms -/

example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ (c ↦₆₄ z)) :
    ∃ Fr, m ⊨ (b ↦₆₄ y) ∗ Fr ∧ Fr = ((a ↦₆₄ x) ∗ (c ↦₆₄ z)) := by
  refine ⟨_, ?_, rfl⟩
  sep_entail

/-- Ghost values are instantiated by unification. -/
example (h : m ⊨ (a ↦₆₄ x) ∗ R) : ∃ v, m ⊨ (a ↦₆₄ v) ∗ R ∧ v = x := by
  refine ⟨_, ?_, rfl⟩
  sep_entail

example (hx : x = 7#64) (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ ⌜x = 7#64⌝ ∗ (a ↦₆₄ x) ∗ R := by
  sep_entail

example (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ R ∗ (∃∗ v, ((a ↦₆₄ v) ∗ ⌜v = x⌝)) := by
  sep_entail

/-! ## `sep_focus`, Framed Reads, and `sep_facts` -/

example : ((a ↦₆₄ x) ∗ (b ↦₈ 1#8) ∗ R) = (b ↦₈ 1#8) ∗ ((a ↦₆₄ x) ∗ R) := by
  sep_focus

example (h : m ⊨ R ∗ (a ↦₆₄ x) ∗ (b ↦₃₂ 9#32)) : m.read64 a = x :=
  read64_sep_at a h

example (ws : List (BitVec 64)) (i : BitVec 64) (hi : i.toNat < ws.length)
    (h : m ⊨ R ∗ (a ↦₆₄* ws) ∗ F) :
    m.read64 (a + (i <<< 3)) = ws.getD i.toNat 0#64 :=
  read64_shl3_of_words_at a h i hi

example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₁₂₈ 5#128) ∗ (c ↦₈ 7#8) ∗ R) :
    m.read64 a = x ∧
    m.read64 b = (5#128).extractLsb' 0 64 ∧
    m.read64 (b + 8#64) = (5#128).extractLsb' 64 64 ∧
    m.read8 c = 7#8 ∧
    DisjointRegions a 8 b 16 ∧
    DisjointRegions a 8 c 1 := by
  sep_facts h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> with_reducible assumption

/-! ## `arm64_sep_close`: Store Stepping and Region Updates -/

/-- Exact-width stores across 8, 16, 32, 64, and 128-bit blocks in a single goal. -/
example (a8 a16 a32 a64 a128 : BitVec 64)
    (v8 w8 : BitVec 8) (v16 w16 : BitVec 16) (v32 w32 : BitVec 32)
    (v64 w64 : BitVec 64) (v128 w128 : BitVec 128)
    (h : m ⊨ (a8 ↦₈ v8) ∗ (a16 ↦₁₆ v16) ∗ (a32 ↦₃₂ v32) ∗ (a64 ↦₆₄ v64) ∗ (a128 ↦₁₂₈ v128) ∗ R) :
    ((((m.write8 a8 w8).write16 a16 w16).write32 a32 w32).write64 a64 (w64 + 0#64)).write128 a128 w128 ⊨
      R ∗ (a128 ↦₁₂₈ w128) ∗ (a64 ↦₆₄ w64) ∗ (a32 ↦₃₂ w32) ∗ (a16 ↦₁₆ w16) ∗ (a8 ↦₈ w8) := by
  arm64_sep_close

/-- Batched stores inside a `memRegion` and a `stackFrame16At` via `AgreesOutside`. -/
example (sp0 : BitVec 64) (h : m ⊨ memRegion a 24 ∗ stackFrame16At sp0 ∗ R) :
    (((m.write64 a x).write64 (a + 8#64) y).write64 (sp0 - 16#64) z).write64 (sp0 - 8#64) x ⊨
      R ∗ stackFrame16At sp0 ∗ memRegion a 24 := by
  arm64_sep_close

/-- Partial store inside a typed 128-bit cell weakens it to `memRegion`. -/
example (v : BitVec 128) (w : BitVec 32) (h : m ⊨ (a ↦₁₂₈ v) ∗ R) :
    m.write32 (a + 4#64) w ⊨ R ∗ memRegion a 16 := by
  arm64_sep_close

/-- Existential witness instantiation combined with `arm64_sep_close`. -/
example (h : m ⊨ (a ↦₆₄ x) ∗ R) :
    ∃ v', m.write64 a (x + 1#64) ⊨ R ∗ (a ↦₆₄ v') ∧ v' = x + 1#64 := by
  arm64_instantiate_sep_exists
  exact ⟨by arm64_sep_close, rfl⟩

/-! ## `SepWP` Access Witnesses, Frame Splitting, and Rewrites -/

example : SepLoad8 b ((a ↦₆₄ x) ∗ (b ↦₈ 4#8) ∗ R) 4#8 := by
  wp_sep_access

example : SepLoad64 a (R ∗ (a ↦₆₄ x) ∗ F) x := by
  wp_sep_access

example : SepStore8 a 9#8 ((a ↦₈ 1#8) ∗ R) ((a ↦₈ 9#8) ∗ R) := by
  wp_sep_access

example : SepStore64 a y (R ∗ (a ↦₆₄ x)) (R ∗ (a ↦₆₄ y)) := by
  wp_sep_access

example : SepFrame (b ↦₆₄ y) ((a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ R) ((a ↦₆₄ x) ∗ R) := by
  wp_sep_access

example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ R) :
    ∃ F', m ⊨ (b ↦₆₄ y) ∗ (F' ∗ R) ∧ F' = (a ↦₆₄ x) := by
  refine ⟨_, ?_, rfl⟩
  wp_frame_split

example (h : m ⊨ R ∗ (a ↦₆₄ x) ∗ (b ↦₈ 5#8)) :
    m.read64 a + BitVec.zeroExtend 64 (m.read8 b) = x + 5#64 := by
  wp_rewrite_reads
  rfl

example (hcond : x = 0#64) (h : m ⊨ (a ↦₆₄ x) ∗ R) :
    m ⊨ (a ↦₆₄ (if x == 0#64 then 0#64 else 1#64)) ∗ R := by
  wp_resolve_ites
  sep_entail

/-! ## End-to-End `SepWP` Proofs with Framed Subroutine Calls -/

@[simp, arm64_norm] def bump_cell_addr : BitVec 64 := 0x10000#64
@[simp, arm64_norm] def bump_pair_addr : BitVec 64 := 0x10010#64

/-- Leaf subroutine `bump_cell`: reads `v` at `[x0]`, writes `v + 1` back to `[x0]`, returns. -/
def bumpCellCode : FnCode :=
  .atAddr "bump_cell" bump_cell_addr
    ("f9400001 " ++ -- 0x10000: ldr x1, [x0]
     "91000421 " ++ -- 0x10004: add x1, x1, #1
     "f9000001 " ++ -- 0x10008: str x1, [x0]
     "d65f03c0")    -- 0x1000c: ret

abbrev BumpCellCodeAt (prog : Program) : Prop :=
  bumpCellCode.holds prog

abbrev bumpCellSpec : Spec (BitVec 64 × BitVec 64) where
  pre  := fun (p, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v)
  post := fun (p, v) _ _sf => (p ↦₆₄ (v + 1#64))

/-- Leaf contract for `bump_cell`, verified by `wp_init` + `wp_steps` + `wp_done` and called from
    `bump_pair_ok` below. -/
theorem bump_cell_ok (prog : Program) (h_code : BumpCellCodeAt prog) :
    prog.subroutineOk "bump_cell" bumpCellSpec := by
  wp_init pv s0
  wp_steps
  wp_done

/-- Caller `bump_pair`: saves `(x19, x30)` on the stack, calls `bump_cell(p)` and `bump_cell(q)`,
    restores `(x19, x30)`, and returns. -/
def bumpPairCode : FnCode :=
  .atAddr "bump_pair" bump_pair_addr
    ("a9bf7bf3 " ++ -- 0x10010: stp x19, x30, [sp, #-16]!
     "91000033 " ++ -- 0x10014: add x19, x1, #0
     "97fffffa " ++ -- 0x10018: bl 0x10000 (bump_cell)
     "91000260 " ++ -- 0x1001c: add x0, x19, #0
     "97fffff8 " ++ -- 0x10020: bl 0x10000 (bump_cell)
     "a8c17bf3 " ++ -- 0x10024: ldp x19, x30, [sp], #16
     "d65f03c0")    -- 0x10028: ret

abbrev BumpPairCodeAt (prog : Program) : Prop :=
  bumpPairCode.holds prog

structure BumpPairArgs where
  p : BitVec 64
  q : BitVec 64
  v : BitVec 64
  w : BitVec 64

abbrev bumpPairSpec : Spec BumpPairArgs where
  pre  := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.p ∧ s0.readReg64 .x1 = a.q⌝ ∗
    (a.p ↦₆₄ a.v) ∗ (a.q ↦₆₄ a.w) ∗ stackFrame16 s0
  post := fun a _ sf =>
    (a.p ↦₆₄ (a.v + 1#64)) ∗ (a.q ↦₆₄ (a.w + 1#64)) ∗ stackFrame16 sf

/-- Verified by `SepWP`: each `wp_call h_bump` automatically frames the other cell and the caller's
    saved stack slots across the call via `SepWP.call_subroutine_frame` and `wp_frame_split`. -/
theorem bump_pair_ok (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellSpec) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps
  wp_call h_bump
  wp_steps
  wp_call h_bump
  wp_steps
  wp_done

/-! ## `wp_call` Dispatch on `Spec.split` (`specIsSplit`) -/

/-- A user-defined alias for a `Spec.split` contract. -/
def splitAliasSpec : Spec (BitVec 64) :=
  Spec.split (fun a s0 => s0.readReg64 .x0 = a) (fun _ => emp)
    (fun a _ sf => sf.readReg64 .x0 = a) (fun _ => emp)

/-- Callee contracts exercised by the `wp_call` dispatch test below. -/
def splitAliasCall : Prop := ∀ prog entry, subroutine_ok prog entry splitAliasSpec
def rustSretCall : Prop := ∀ prog entry, subroutine_ok prog entry
  (Spec.rustSret (α := Unit) (fun _ _ _ _ => True) (fun _ _ _ => emp)
    (fun _ _ _ _ _ => True) (fun _ _ _ => emp))
def fnSplitAliasCall : Prop := ∀ prog, fn_subroutine_ok prog "f" splitAliasSpec
def plainCall : Prop := ∀ prog entry, subroutine_ok prog entry bumpPairSpec

/- `wp_call` must dispatch to `SepWP.call_sep` for `Spec.split` contracts hidden behind a `def`
   (`splitAliasSpec`, `Spec.rustSret`) and for the `fn_subroutine_ok` abbrev, but not for a plain
   `Spec` structure literal. -/
open Lean Meta in
run_meta do
  let check (decl : Name) (expected : Bool) : MetaM Unit := do
    forallTelescope (← getConstInfo decl).value! fun _ body => do
      let ty ← whnfR body
      unless ty.isAppOfArity ``Arm64.subroutine_ok 4 do
        throwError "{decl}: expected `subroutine_ok` after `whnfR`, got{indentExpr ty}"
      let got ← specIsSplit (ty.getArg! 3)
      unless got == expected do
        throwError "{decl}: specIsSplit returned {got}, expected {expected}"
  check ``splitAliasCall true
  check ``rustSretCall true
  check ``fnSplitAliasCall true
  check ``plainCall false

/-! ## First-Class 32-Bit Cells (`↦₃₂`) in `SepWP` -/

section PointsTo32

variable (u v w : BitVec 32)

/-- A lone `u32` field next to 64-bit cells (no `↦₆₄` cell covers it). -/
example : SepLoad32 (a + 32#64) ((a ↦₆₄ x) ∗ ((a + 32#64) ↦₃₂ u) ∗ R) u := by
  wp_sep_access

/-- The access address is matched with the atom address up to literal-offset arithmetic. -/
example : SepLoad32 ((b - 48#64) + 12#64) (R ∗ ((b - 36#64) ↦₃₂ u)) u := by
  wp_sep_access

example : SepLoad32 ((a + 32#64) + 4#64) (((a + 32#64) ↦₃₂ u) ∗ ((a + 36#64) ↦₃₂ v) ∗ R) v := by
  wp_sep_access

example : SepStore32 (a + 36#64) w (((a + 32#64) ↦₃₂ u) ∗ ((a + 36#64) ↦₃₂ v) ∗ R)
    (((a + 32#64) ↦₃₂ u) ∗ ((a + 36#64) ↦₃₂ w) ∗ R) := by
  wp_sep_access

/-- A store at a normalized address keeps the atom's own address form. -/
example : SepStore32 ((b - 48#64) + 12#64) w (((b - 36#64) ↦₃₂ u) ∗ R) (((b - 36#64) ↦₃₂ w) ∗ R) := by
  wp_sep_access

/-- No `↦₃₂` atom: the 32-bit lookup fails (so `wp_step` falls back to the 64-bit-half rules). -/
example : (a ↦₆₄ x) ∗ R = (a ↦₆₄ x) ∗ R := by
  fail_if_success have : SepLoad32 a ((a ↦₆₄ x) ∗ R) 0#32 := by wp_sep_access
  rfl

end PointsTo32

@[simp, arm64_norm] def bump_index_addr : BitVec 64 := 0x10100#64
@[simp, arm64_norm] def swap_u32_pair_addr : BitVec 64 := 0x10200#64

/-- `bump_index`: a 36-byte record `{ key : [u8; 32], index : u32 }` at `x0` (only the first key
    word is modelled) followed by a `u32` accumulator at `x0 + 36`. Increments `index` (offset 32,
    a lone `u32` that shares no 8-byte cell with a known neighbour) and adds it to the
    accumulator (offset 36, not 8-byte aligned). -/
def bumpIndexCode : FnCode :=
  .atAddr "bump_index" bump_index_addr
    ("b9402001 " ++ -- 0x10100: ldr  w1, [x0, #32]
     "11000421 " ++ -- 0x10104: add  w1, w1, #1
     "b9002001 " ++ -- 0x10108: str  w1, [x0, #32]
     "b8424002 " ++ -- 0x1010c: ldur w2, [x0, #36]
     "0b010042 " ++ -- 0x10110: add  w2, w2, w1
     "b8024002 " ++ -- 0x10114: stur w2, [x0, #36]
     "d65f03c0")    -- 0x10118: ret

abbrev BumpIndexCodeAt (prog : Program) : Prop :=
  bumpIndexCode.holds prog

structure BumpIndexArgs where
  p : BitVec 64
  key0 : BitVec 64
  idx : BitVec 32
  acc : BitVec 32

abbrev bumpIndexSpec : Spec BumpIndexArgs where
  pre  := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.p⌝ ∗
    (a.p ↦₆₄ a.key0) ∗ ((a.p + 32#64) ↦₃₂ a.idx) ∗ ((a.p + 36#64) ↦₃₂ a.acc)
  post := fun a _ _sf =>
    (a.p ↦₆₄ a.key0) ∗ ((a.p + 32#64) ↦₃₂ (a.idx + 1#32)) ∗
    ((a.p + 36#64) ↦₃₂ (a.acc + (a.idx + 1#32)))

/-- Load, increment, and store through `↦₃₂` atoms (`SepWP.step_ldr32`, `step_str32`,
    `step_ldur32`, `step_stur32`). -/
theorem bump_index_ok (prog : Program) (h_code : BumpIndexCodeAt prog) :
    prog.subroutineOk "bump_index" bumpIndexSpec := by
  wp_init a s0
  wp_steps
  wp_done

/-- `swap_u32_pair`: swaps the two `u32` cells at `x0 + 4` and `x0 + 8` with a 32-bit `ldp`/`stp`
    (the second element's address `(x0 + 4) + 4` is matched with the atom at `x0 + 8`); the
    intermediate `ldrsw` exercises `SepWP.step_ldrsw32`. -/
def swapU32PairCode : FnCode :=
  .atAddr "swap_u32_pair" swap_u32_pair_addr
    ("29408801 " ++ -- 0x10200: ldp   w1, w2, [x0, #4]
     "b9800803 " ++ -- 0x10204: ldrsw x3, [x0, #8]
     "29008402 " ++ -- 0x10208: stp   w2, w1, [x0, #4]
     "d65f03c0")    -- 0x1020c: ret

abbrev SwapU32PairCodeAt (prog : Program) : Prop :=
  swapU32PairCode.holds prog

structure SwapU32PairArgs where
  p : BitVec 64
  u : BitVec 32
  v : BitVec 32

abbrev swapU32PairSpec : Spec SwapU32PairArgs where
  pre  := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.p⌝ ∗ ((a.p + 4#64) ↦₃₂ a.u) ∗ ((a.p + 8#64) ↦₃₂ a.v)
  post := fun a _ _sf =>
    ((a.p + 4#64) ↦₃₂ a.v) ∗ ((a.p + 8#64) ↦₃₂ a.u)

theorem swap_u32_pair_ok (prog : Program) (h_code : SwapU32PairCodeAt prog) :
    prog.subroutineOk "swap_u32_pair" swapU32PairSpec := by
  wp_init a s0
  wp_steps
  wp_done

/-! ## `ldrsw` High-Half 64-Bit Load and Structure-Typed `wp_call` -/

@[simp, arm64_norm] def ldrsw_hi_callee_addr : BitVec 64 := 0x10300#64
@[simp, arm64_norm] def ldrsw_hi_caller_addr : BitVec 64 := 0x10310#64

structure HiCallState where
  ptr  : BitVec 64
  word : BitVec 64
  tag  : BitVec 64

/-- Callee reading the high 32-bit half of `ptr ↦₆₄ word` with `ldrsw x0, [x0, #4]`. -/
def ldrswHiCalleeCode : FnCode :=
  .atAddr "ldrsw_hi_callee" ldrsw_hi_callee_addr
    ("b9800400 " ++ -- 0x10300: ldrsw x0, [x0, #4]
     "d65f03c0")    -- 0x10304: ret

abbrev LdrswHiCalleeCodeAt (prog : Program) : Prop :=
  ldrswHiCalleeCode.holds prog

def ldrswHiCalleeSpec : Spec HiCallState :=
  Spec.split
    (fun v s0 => s0.readReg64 .x0 = v.ptr ∧ v.tag ≠ 0#64)
    (fun v => (v.ptr ↦₆₄ v.word) ∗ ((v.ptr + 8#64) ↦₆₄ v.tag))
    (fun v _ sf => sf.readReg64 .x0 = BitVec.signExtend 64 (BitVec.truncate 32 (v.word >>> 32)))
    (fun v => (v.ptr ↦₆₄ v.word) ∗ ((v.ptr + 8#64) ↦₆₄ v.tag))

theorem ldrsw_hi_callee_ok (prog : Program) (h_code : LdrswHiCalleeCodeAt prog) :
    prog.subroutineOk "ldrsw_hi_callee" ldrswHiCalleeSpec := by
  wp_init v s0
  wp_steps
  wp_done

def ldrswHiCallerCode : FnCode :=
  .atAddr "ldrsw_hi_caller" ldrsw_hi_caller_addr
    ("a9bf7bfd " ++ -- 0x10310: stp x29, x30, [sp, #-16]!
     "97fffffb " ++ -- 0x10314: bl 0x10300 (ldrsw_hi_callee)
     "a8c17bfd " ++ -- 0x10318: ldp x29, x30, [sp], #16
     "d65f03c0")    -- 0x1031c: ret

abbrev LdrswHiCallerCodeAt (prog : Program) : Prop :=
  ldrswHiCallerCode.holds prog

abbrev ldrswHiCallerSpec : Spec HiCallState where
  pre  := fun v s0 =>
    ⌜s0.readReg64 .x0 = v.ptr ∧ v.tag ≠ 0#64⌝ ∗
    (v.ptr ↦₆₄ v.word) ∗ ((v.ptr + 8#64) ↦₆₄ v.tag) ∗ stackFrame16 s0
  post := fun v _ sf =>
    ⌜sf.readReg64 .x0 = BitVec.signExtend 64 (BitVec.truncate 32 (v.word >>> 32))⌝ ∗
    (v.ptr ↦₆₄ v.word) ∗ ((v.ptr + 8#64) ↦₆₄ v.tag) ∗ stackFrame16 sf

theorem ldrsw_hi_caller_ok (prog : Program) (h_code : LdrswHiCallerCodeAt prog)
    (h_addr : prog.fnAddr "ldrsw_hi_callee" = ldrsw_hi_callee_addr)
    (h_callee : prog.subroutineOk "ldrsw_hi_callee" ldrswHiCalleeSpec) :
    prog.subroutineOk "ldrsw_hi_caller" ldrswHiCallerSpec := by
  wp_init v s0
  wp_steps
  wp_call h_callee
  wp_steps
  wp_done

/-! ## Fail-Fast Diagnostics, Offset Folding, and Step/Call Checks -/

section FailFastTests

/-- Wraps the current goal type in an `Expr.mdata` node. -/
elab "test_wrap_mdata_goal" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← g.getType
  let kv := Lean.KVMap.empty.insert `test_mdata true
  let g' ← g.replaceTargetDefEq (Lean.mkMData kv t)
  Lean.Elab.Tactic.replaceMainGoal [g']

/-! ### Offset Folding in Frame Matching -/

set_option maxHeartbeats 20000 in
example (s0 sf : State) (hsp : sf.sp = s0.sp - 80#64) :
    ∃ F, SepFrame
      ((sf.sp - 16#64) ↦₆₄ x ∗ ((s0.sp - 36#64) ↦₆₄ y))
      (((s0.sp - 80#64) - 16#64) ↦₆₄ x ∗ ((s0.sp - 48#64 + 12#64) ↦₆₄ y) ∗ R)
      F ∧ F = R := by
  refine ⟨_, ?_, rfl⟩
  wp_frame_split

set_option maxHeartbeats 20000 in
example (s0 sf : State) (hsp : sf.sp = s0.sp - 80#64)
    (h : m ⊨ ((s0.sp - 80#64) - 16#64) ↦₆₄ x ∗ ((s0.sp - 48#64 + 12#64) ↦₆₄ y) ∗ R) :
    ∃ F', m ⊨ (sf.sp - 16#64) ↦₆₄ x ∗ ((s0.sp - 36#64) ↦₆₄ y) ∗ (F' ∗ R) ∧ F' = emp := by
  refine ⟨_, ?_, rfl⟩
  wp_frame_split

set_option maxHeartbeats 20000 in
example (s0 : State) :
    ∃ F, SepFrame
      ((s0.sp - 16#64) ↦₆₄ x ∗ ((s0.sp - 24#64) ↦₆₄ y))
      (((s0.sp + 32#64) - 48#64) ↦₆₄ x ∗ ((s0.sp + (-24#64)) ↦₆₄ y) ∗ R)
      F ∧ F = R := by
  refine ⟨_, ?_, rfl⟩
  wp_frame_split

/-! ### `mdata`-Wrapped Goals -/

set_option maxHeartbeats 20000 in
example (s0 : State) :
    ∃ F, SepFrame ((s0.sp - 24#64) ↦₆₄ x) (((s0.sp - 16#64) - 8#64) ↦₆₄ x ∗ R) F ∧ F = R := by
  refine ⟨_, ?_, rfl⟩
  test_wrap_mdata_goal
  wp_frame_split

set_option maxHeartbeats 20000 in
example (h : m ⊨ ((a - 16#64) - 8#64) ↦₆₄ x ∗ R) :
    m ⊨ R ∗ ((a - 24#64) ↦₆₄ x) := by
  test_wrap_mdata_goal
  sep_entail

/-! ### Frame-Split Diagnostics -/

/--
error: frame_split: no match for stackFrame64
  s0 (note: `stackFrame64` is a local variable — possible typo or auto-bound implicit) in precondition; candidates: (s0.sp -
    64#64) ↦₆₄
  y
-/
#guard_msgs (substring := true) in
set_option maxHeartbeats 15000 in
example (s0 : State) (stackFrame64 : State → SepProp) :
    SepFrame (stackFrame64 s0 ∗ (a ↦₆₄ x))
      (((s0.sp - 64#64) ↦₆₄ y) ∗ (a ↦₆₄ x)) emp := by
  wp_frame_split

/--
error: frame_split: all concrete atoms matched, but the target still contains unassigned metavariable atom(s)
-/
#guard_msgs (substring := true) in
set_option maxHeartbeats 15000 in
example : ∃ Q : SepProp, ((a ↦₆₄ x) ∗ (b ↦₆₄ y)) = ((a ↦₆₄ x) ∗ Q) ∗ emp := by
  apply Exists.intro
  sep_focus

/--
(a + 8#64) ↦₆₄ x, … (+2 more)
-/
#guard_msgs (substring := true) in
set_option maxHeartbeats 20000 in
example : SepFrame (c ↦₆₄ z)
    (((a + 1#64) ↦₆₄ x) ∗ ((a + 2#64) ↦₆₄ x) ∗ ((a + 3#64) ↦₆₄ x) ∗ ((a + 4#64) ↦₆₄ x) ∗
     ((a + 5#64) ↦₆₄ x) ∗ ((a + 6#64) ↦₆₄ x) ∗ ((a + 7#64) ↦₆₄ x) ∗ ((a + 8#64) ↦₆₄ x) ∗
     ((a + 9#64) ↦₆₄ x) ∗ ((a + 10#64) ↦₆₄ x)) emp := by
  wp_frame_split

/-! ### Postcondition Value Mismatch in `wp_done` -/

@[simp, arm64_norm] def ret_const_addr : BitVec 64 := 0x10400#64

def retConstCode : FnCode :=
  .atAddr "ret_const" ret_const_addr
    ("d2800540 " ++ -- 0x10400: mov x0, #42
     "d65f03c0")    -- 0x10404: ret

abbrev RetConstCodeAt (prog : Program) : Prop :=
  retConstCode.holds prog

abbrev retConstWrongSpec : Spec Unit where
  pre  := fun _ _s0 => emp
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 99#64⌝

/--
error: wp_done: postcondition value mismatch:
  actual:   42#64
  expected: 99#64
-/
#guard_msgs (error, drop info, substring := true) in
set_option maxHeartbeats 20000 in
example (prog : Program) (h_code : RetConstCodeAt prog) :
    prog.subroutineOk "ret_const" retConstWrongSpec := by
  wp_init _u s0
  wp_steps
  wp_done

/-! ### Tail-Call Boundary in `wp_steps` -/

@[simp, arm64_norm] def tail_target_addr : BitVec 64 := 0x10500#64
@[simp, arm64_norm] def tail_caller_addr : BitVec 64 := 0x10510#64

def tailTargetCode : FnCode :=
  .atAddr "tail_target" tail_target_addr
    ("d2800020 " ++ -- 0x10500: mov x0, #1
     "d65f03c0")    -- 0x10504: ret

def tailCallerCode : FnCode :=
  .atAddr "tail_caller" tail_caller_addr
    ("d2800000 " ++ -- 0x10510: mov x0, #0
     "17fffffb")    -- 0x10514: b 0x10500 (tail_target)

abbrev TailBothCodeAt (prog : Program) : Prop :=
  tailTargetCode.holds prog ∧ tailCallerCode.holds prog

abbrev tailCallerSpec : Spec Unit where
  pre  := fun _ _s0 => emp
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64⌝

/--
info: wp_steps: stopped at pc 66816#64 (target s0.readReg64 Reg.lr): stopped at function entry / tail-call boundary; next: use `wp_tailcall <callee_spec>` (or `wp_step` to inline)
-/
#guard_msgs (info, whitespace := lax, substring := true) in
set_option proofLib.wpVerbose true in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : TailBothCodeAt prog) :
    prog.subroutineOk "tail_caller" tailCallerSpec := by
  rcases h_code with ⟨_h_target, _h_caller⟩
  wp_init _u s0
  wp_steps
  wp_step
  wp_step
  wp_done

/-! ### Conditional Branch Resolution in `wp_steps` -/

@[simp, arm64_norm] def branch_fn_addr : BitVec 64 := 0x10600#64

def branchFnCode : FnCode :=
  .atAddr "branch_fn" branch_fn_addr
    ("b4000060 " ++ -- 0x10600: cbz x0, 0x1060c
     "d2800020 " ++ -- 0x10604: mov x0, #1
     "d65f03c0 " ++ -- 0x10608: ret
     "d2800040 " ++ -- 0x1060c: mov x0, #2
     "d65f03c0")    -- 0x10610: ret

abbrev BranchFnCodeAt (prog : Program) : Prop :=
  branchFnCode.holds prog

abbrev branchFnNonzeroSpec : Spec (BitVec 64) where
  pre  := fun v s0 => ⌜s0.readReg64 .x0 = v ∧ (v == 0#64) = false⌝
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64⌝

set_option maxHeartbeats 40000 in
theorem branch_fn_nonzero_ok (prog : Program) (h_code : BranchFnCodeAt prog) :
    prog.subroutineOk "branch_fn" branchFnNonzeroSpec := by
  wp_init v s0
  wp_steps
  wp_done

abbrev branchFnUnresolvedSpec : Spec (BitVec 64) where
  pre  := fun v s0 => ⌜s0.readReg64 .x0 = v⌝
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64 ∨ sf.readReg64 .x0 = 2#64⌝

/--
info: wp_steps: stopped at pc
-/
#guard_msgs (info, substring := true) in
set_option proofLib.wpVerbose true in
set_option maxHeartbeats 40000 in
theorem branch_fn_unresolved_ok (prog : Program) (h_code : BranchFnCodeAt prog) :
    prog.subroutineOk "branch_fn" branchFnUnresolvedSpec := by
  wp_init v s0
  wp_steps
  wp_if h_z
  · wp_steps; wp_done
  · wp_steps; wp_done

set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : RetConstCodeAt prog) :
    prog.subroutineOk "ret_const" {
      pre  := fun (_ : Unit) _s0 => emp
      post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝
    } := by
  wp_init _u s0
  wp_steps 1
  wp_steps 1
  wp_done

/-! ### `wp_call`, `wp_step`, and `wp_done` Diagnostics -/

structure UnderdetGhost where
  ptr   : BitVec 64
  extra : BitVec 64

def underdetCalleeSpec : Spec UnderdetGhost :=
  Spec.split
    (fun g s0 => s0.readReg64 .x0 = g.ptr ∧ g.extra.toNat + 46884 < 100000)
    (fun g => g.ptr ↦₆₄ 0#64)
    (fun _ _ _ => True)
    (fun g => g.ptr ↦₆₄ 0#64)

/--
error: wp_call: underdetermined ghost variable(s) [extra] in callee precondition conjunct:
-/
#guard_msgs (error, drop info, substring := true) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : LdrswHiCallerCodeAt prog)
    (h_addr : prog.fnAddr "ldrsw_hi_callee" = ldrsw_hi_callee_addr)
    (h_callee : prog.subroutineOk "ldrsw_hi_callee" underdetCalleeSpec) :
    prog.subroutineOk "ldrsw_hi_caller" {
      pre  := fun (p : BitVec 64) s0 =>
        ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ 0#64) ∗ stackFrame16 s0
      post := fun _ _ _ => emp
    } := by
  wp_init p s0
  wp_steps
  wp_call h_callee

/--
error: wp_step: no step rule succeeded for instruction
-/
#guard_msgs (error, drop info, substring := true) in
set_option maxHeartbeats 25000 in
example (prog : Program) (h_code : BumpCellCodeAt prog) :
    prog.subroutineOk "bump_cell" {
      pre  := fun (p : BitVec 64) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ ((p + 64#64) ↦₆₄ 0#64)
      post := fun _ _ _ => emp
    } := by
  wp_init p s0
  wp_step

/--
error: wp_done: postcondition memory mismatch at `p`:
  actual:   43#64
  expected: 99#64
-/
#guard_msgs (error, drop info, substring := true) in
set_option maxHeartbeats 25000 in
example (prog : Program) (h_code : BumpCellCodeAt prog) :
    prog.subroutineOk "bump_cell" {
      pre  := fun (p : BitVec 64) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ 42#64)
      post := fun (p : BitVec 64) _ _ => p ↦₆₄ 99#64
    } := by
  wp_init p s0
  wp_steps
  wp_done

def boundedCalleeSpec : Spec (BitVec 64) :=
  Spec.split
    (fun p s0 => s0.readReg64 .x0 = p ∧ p.toNat + 16 < 1000)
    (fun p => p ↦₆₄ 0#64)
    (fun _ _ _ => True)
    (fun p => p ↦₆₄ 0#64)

set_option maxHeartbeats 35000 in
example (prog : Program) (h_code : LdrswHiCallerCodeAt prog)
    (h_addr : prog.fnAddr "ldrsw_hi_callee" = ldrsw_hi_callee_addr)
    (h_callee : prog.subroutineOk "ldrsw_hi_callee" boundedCalleeSpec) :
    prog.subroutineOk "ldrsw_hi_caller" {
      pre  := fun (p : BitVec 64) s0 =>
        ⌜s0.readReg64 .x0 = p ∧ p.toNat < 500⌝ ∗ (p ↦₆₄ 0#64) ∗ stackFrame16 s0
      post := fun (p : BitVec 64) _ sf => (p ↦₆₄ 0#64) ∗ stackFrame16 sf
    } := by
  wp_init p s0
  wp_steps
  wp_call h_callee
  wp_steps
  wp_done

/--
error: wp_call: failed to prove callee precondition conjunct:
-/
#guard_msgs (error, drop info, substring := true) in
set_option maxHeartbeats 35000 in
example (prog : Program) (h_code : LdrswHiCallerCodeAt prog)
    (h_addr : prog.fnAddr "ldrsw_hi_callee" = ldrsw_hi_callee_addr)
    (h_callee : prog.subroutineOk "ldrsw_hi_callee" boundedCalleeSpec) :
    prog.subroutineOk "ldrsw_hi_caller" {
      pre  := fun (p : BitVec 64) s0 =>
        ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ 0#64) ∗ stackFrame16 s0
      post := fun _ _ _ => emp
    } := by
  wp_init p s0
  wp_steps
  wp_call h_callee

set_option maxHeartbeats 25000 in
example (prog : Program) (h_code : RetConstCodeAt prog) :
    prog.subroutineOk "ret_const" {
      pre  := fun (_ : Unit) _s0 => emp
      post := fun _ s0 sf => ⌜sf.readReg64 .x0 = 42#64 ∧ CalleeSavedPreserved s0 sf⌝
    } := by
  wp_init _u s0
  wp_steps
  wp_done

/-! ### Target-Address Mismatch Diagnostics in `wp_call` -/

section TargetMismatchDiagTest
open ProofLib.ProgramReflection

register_fn_entry "ldrsw_hi_callee" ldrswHiCalleeCode ldrswHiCalleeCode ldrsw_hi_callee_addr 0x10300 8
register_fn_entry "ret_const" retConstCode retConstCode ret_const_addr 0x10400 8

/--
error: wp_call: call target address does not match callee entry: h_wrong is the wrong contract (expected entry 0x10300#64 ("ldrsw_hi_callee") / got 0x10400#64 ("ret_const"))
  call target PC: 0x10300#64 (registered entry: "ldrsw_hi_callee" at 0x10300)
  callee entry:   0x10400#64 (registered entry: "ret_const" at 0x10400)
  raw target PC:  66304#64
  raw callee:     prog.fnAddr "ret_const"
hint: ensure execution has stepped to the `BL` call site (`wp_steps` / `wp_sym_steps`) and pass the contract matching the call target PC
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : LdrswHiCallerCodeAt prog)
    (h_addr : prog.fnAddr "ret_const" = ret_const_addr)
    (h_wrong : prog.subroutineOk "ret_const" retConstWrongSpec) :
    prog.subroutineOk "ldrsw_hi_caller" {
      pre  := fun (p : BitVec 64) s0 =>
        ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ 0#64) ∗ stackFrame16 s0
      post := fun _ _ _ => emp
    } := by
  wp_init p s0
  wp_steps
  wp_call h_wrong

/--
error: wp_call: call target address does not match callee entry: stepping stopped early (halted at 0x10310#64 (stp x29, x30, [sp, #-16]!), 1 instruction before the call)
  call target PC: 0x10310#64 (callee: "ldrsw_hi_caller")
  callee entry:   0x10400#64 (registered entry: "ret_const" at 0x10400)
  raw target PC:  prog.fnAddr "ldrsw_hi_caller"
  raw callee:     prog.fnAddr "ret_const"
  caller insn:    Instr.stp RegWidth.W64 (Reg.gpr 29#5) (Reg.gpr 30#5) (AddrMode.PreIndex Reg.sp (-16#64))
hint: execution is currently stopped at caller instruction `Instr.stp RegWidth.W64 (Reg.gpr 29#5) (Reg.gpr 30#5) (AddrMode.PreIndex Reg.sp (-16#64))` at `0x10310#64` (`wp_steps` / `wp_sym_steps` stopped early before reaching the call target); run `wp_step` or `set_option proofLib.wpVerbose true` to see why stepping stopped
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : LdrswHiCallerCodeAt prog)
    (h_addr : prog.fnAddr "ret_const" = ret_const_addr)
    (h_wrong : prog.subroutineOk "ret_const" retConstWrongSpec) :
    prog.subroutineOk "ldrsw_hi_caller" {
      pre  := fun (p : BitVec 64) s0 =>
        ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ 0#64) ∗ stackFrame16 s0
      post := fun _ _ _ => emp
    } := by
  wp_init p s0
  wp_call h_wrong

set_option maxHeartbeats 40000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry + 0xfffffffffffffe5c#64)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry - 0x1a4#64)
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 7#64) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 7#64) := by
  wp_call h_callee ()
  exact SepWP.done (by assumption) (by assumption) (by assumption)

end TargetMismatchDiagTest

/-! ### Unresolved Conditional Branch Diagnostics in `wp_call` and `wp_done` -/

/--
error: wp_call: current PC is an unresolved conditional branch:
  condition: (v == 0#64) = true
  then PC:   0x1060c#64
  else PC:   0x10604#64
hint: if both branches are reachable, split with `wp_if hcond` (or `wp_if_join <join_pc> <inv>` for diamond control flow); if only one branch is feasible, prove `have hcond : <cond> = true := by bv_omega` (or `= false`) before `wp_steps` / `wp_sym_steps`, or simplify the current PC with `wp_simp_pre [hcond]`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : BranchFnCodeAt prog)
    (h_callee : prog.subroutineOk "ret_const" retConstWrongSpec) :
    prog.subroutineOk "branch_fn" branchFnUnresolvedSpec := by
  wp_init v s0
  wp_steps
  wp_call h_callee

/--
error: wp_done: current PC is an unresolved conditional branch:
  condition: (v == 0#64) = true
  then PC:   0x1060c#64
  else PC:   0x10604#64
hint: if both branches are reachable, split with `wp_if hcond` (or `wp_if_join <join_pc> <inv>` for diamond control flow); if only one branch is feasible, prove `have hcond : <cond> = true := by bv_omega` (or `= false`) before `wp_steps` / `wp_sym_steps`, or simplify the current PC with `wp_simp_pre [hcond]`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : BranchFnCodeAt prog) :
    prog.subroutineOk "branch_fn" branchFnUnresolvedSpec := by
  wp_init v s0
  wp_steps
  wp_done

/-! ### `ult` Loop-Exit Branch Decision in `wp_done` -/

@[simp, arm64_norm] def ult_exit_addr : BitVec 64 := 0x10700#64

/-- Tail of a word-copy loop body: advance the cursor, compare with the end, loop while below. -/
def ultExitCode : FnCode :=
  .atAddr "ult_exit" ult_exit_addr
    ("91002000 " ++ -- 0x10700: add  x0, x0, #8
     "eb01001f " ++ -- 0x10704: cmp  x0, x1
     "54000063 " ++ -- 0x10708: b.lo 0x10714
     "d65f03c0 " ++ -- 0x1070c: ret
     "d2800040 " ++ -- 0x10710: mov  x0, #2
     "d65f03c0")    -- 0x10714: ret

/-- Last iteration: `x0 + 8 = x1`, so `b.lo` falls through and `x0` is the end cursor. -/
abbrev ultExitLastSpec : Spec (BitVec 64 × Nat × Nat) where
  pre := fun ⟨base, d, m⟩ s0 =>
    ⌜s0.readReg64 .x0 = base + BitVec.ofNat 64 (d + 8 * m) ∧
      s0.readReg64 .x1 = base + BitVec.ofNat 64 (d + 8 * (m + 1))⌝
  post := fun ⟨base, d, m⟩ _ sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 (d + 8 * (m + 1))⌝

/-- Earlier iteration `k < m` under a no-overflow bound: `b.lo` is taken. -/
abbrev ultExitEarlySpec : Spec (BitVec 64 × Nat × Nat × Nat) where
  pre := fun ⟨base, d, k, m⟩ s0 =>
    ⌜k < m ∧ base.toNat + d + 8 * (m + 1) < 2 ^ 64 ∧
      s0.readReg64 .x0 = base + BitVec.ofNat 64 (d + 8 * k) ∧
      s0.readReg64 .x1 = base + BitVec.ofNat 64 (d + 8 * (m + 1))⌝
  post := fun _ _ _ => emp

/-- Without the no-overflow bound, `b.lo` is undecidable. -/
abbrev ultExitNoBoundSpec : Spec (BitVec 64 × Nat × Nat × Nat) where
  pre := fun ⟨base, d, k, m⟩ s0 =>
    ⌜k < m ∧ s0.readReg64 .x0 = base + BitVec.ofNat 64 (d + 8 * k) ∧
      s0.readReg64 .x1 = base + BitVec.ofNat 64 (d + 8 * (m + 1))⌝
  post := fun _ _ _ => emp

set_option maxHeartbeats 200000 in
theorem ult_exit_last_ok (prog : Program) (h_code : ultExitCode.holds prog) :
    prog.subroutineOk "ult_exit" ultExitLastSpec := by
  wp_init p s0
  wp_steps
  wp_done

set_option maxHeartbeats 200000 in
theorem ult_exit_early_ok (prog : Program) (h_code : ultExitCode.holds prog) :
    prog.subroutineOk "ult_exit" ultExitEarlySpec := by
  wp_init p s0
  wp_steps
  wp_done

/--
error: wp_done: current PC is an unresolved conditional branch:
-/
#guard_msgs (error, drop info, substring := true) in
set_option maxHeartbeats 200000 in
example (prog : Program) (h_code : ultExitCode.holds prog) :
    prog.subroutineOk "ult_exit" ultExitNoBoundSpec := by
  wp_init p s0
  wp_steps
  wp_done

end FailFastTests

/-! ## C and Rust Specification Combinators (`c_spec` / `rust_spec`) -/

section HighLevelSpecTests

/-! ### Compositional `Spec` Combinators -/

abbrev fn1IdSpec : Spec (BitVec 64) :=
  Spec.fn1 (fun x => x)

abbrev bumpCellCombinatorSpec : Spec (BitVec 64 × BitVec 64) :=
  { pre  := fun (p, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v)
    post := fun (p, v) _ _sf => (p ↦₆₄ (v + 1#64)) }

theorem bump_cell_combinator_framed_ok (prog : Program) (h_code : BumpCellCodeAt prog)
    (q w : BitVec 64) :
    prog.subroutineOk "bump_cell"
      (bumpCellCombinatorSpec.withPreserves (fun _ => q ↦₆₄ w)) :=
  Spec.withPreserves.frame (bump_cell_ok prog h_code) _

/-! ### Declarative `c_spec` and `rust_spec` Macros -/

/-- Tuple-backed `c_spec` with `ptr`, `ghost`, and `ensures`: verified by `SepWP`. -/
abbrev c_spec bumpCellCSpec (p : ptr) (ghost v : BitVec 64)
  requires (p ↦₆₄ v)
  ensures  (p ↦₆₄ (v + 1#64))

theorem bump_cell_cspec_ok (prog : Program) (h_code : BumpCellCodeAt prog) :
    prog.subroutineOk "bump_cell" bumpCellCSpec := by
  wp_init pv s0
  wp_steps
  wp_done

/-- Struct-backed `c_spec` with `stack16`: verified by `SepWP` with framed `wp_call`. -/
abbrev c_spec bumpPairCSpec [a : BumpPairArgs] (a.p : ptr) (a.q : ptr)
  requires (a.p ↦₆₄ a.v) ∗ (a.q ↦₆₄ a.w)
  ensures  (a.p ↦₆₄ (a.v + 1#64)) ∗ (a.q ↦₆₄ (a.w + 1#64))
  stack16

theorem bump_pair_cspec_ok (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellCSpec) :
    prog.subroutineOk "bump_pair" bumpPairCSpec := by
  wp_init a s0
  wp_steps
  wp_call h_bump
  wp_steps
  wp_call h_bump
  wp_steps
  wp_done

/-- Struct-backed `c_spec` with `preserves` and `↦₃₂` cells: verified by `SepWP`. -/
abbrev c_spec bumpIndexCSpec [a : BumpIndexArgs] (a.p : ptr)
  preserves (a.p ↦₆₄ a.key0)
  requires  ((a.p + 32#64) ↦₃₂ a.idx) ∗ ((a.p + 36#64) ↦₃₂ a.acc)
  ensures   let nextIdx := a.idx + 1#32
            ((a.p + 32#64) ↦₃₂ nextIdx) ∗ ((a.p + 36#64) ↦₃₂ (a.acc + nextIdx))

theorem bump_index_cspec_ok (prog : Program) (h_code : BumpIndexCodeAt prog) :
    prog.subroutineOk "bump_index" bumpIndexCSpec := by
  wp_init a s0
  wp_steps
  wp_done

/-- `rust_spec` exercising `slice8`, `sret`, `option_u64`, `niche_u64`, and `panics_when`. -/
rust_spec rustSliceLenSpec (p : slice8 bytes) (ghost bytes : List (BitVec 8)) : usize
  preserves (p ↦ₛ bytes)
  returns   BitVec.ofNat 64 bytes.length

rust_spec rustSretPairSpec (out : sret) (x : u64) (y : u64) (ghost old0 : BitVec 64) (ghost old1 : BitVec 64)
  requires (out ↦₆₄ old0) ∗ ((out + 8#64) ↦₆₄ old1)
  ensures  (out ↦₆₄ x) ∗ ((out + 8#64) ↦₆₄ y)

rust_spec rustOptionU64Spec (x : u64) : option_u64
  returns (if x = 0#64 then 0#32 else 1#32, x)

rust_spec rustNicheNonZeroSpec (x : u64) : niche_u64
  returns (if x = 0#64 then none else some x)

rust_spec rustCheckedIdxSpec (p : slice64 ws) (idx : usize) (ghost ws : List (BitVec 64)) : u64
  preserves   (p ↦₆₄* ws)
  panics_when idx.toNat ≥ ws.length
  returns     ws.getD idx.toNat 0#64

/-- Parameterized `c_spec` with `(ctx ...)`, multi-var `(ghost ...)`, constant/expression register
    arguments `(_ : ty := expr)`, `(sp : sp)`, and named return binding `: (ret : u64)`. -/
c_spec testParamAllocCSpec (ctx pool : SepProp) (ctx base : u64)
    (_ : ptr := 0) (size : u64) (ghost oldCap newCap : u64) (_ : u64 := newCap + 1#64) (sp : sp) : (ret : u64)
  let nextUsed := oldCap + size
  requires_cond size ≤ newCap ∧ newCap < 0x1000#64
  preserves     pool
  requires      (base ↦₆₄ oldCap)
  preserves     memRegion (sp - 64#64) 64
  ensures       if ret = 0 then
                  (base ↦₆₄ oldCap)
                else
                  (ret ↦₆₄ size) ∗ (base ↦₆₄ nextUsed)

/-- Definitional equality check: `testParamAllocCSpec` unfolds to the exact same `Spec` structure
    as a hand-written `def ... : Spec (...) where pre := ... post := ...`. -/
example (pool : SepProp) (base : BitVec 64) :
    testParamAllocCSpec pool base =
      ({ pre := fun (size, oldCap, newCap, sp) s0 =>
           ⌜s0.readReg64 .x0 = 0 ∧ s0.readReg64 .x1 = size ∧
             s0.readReg64 .x2 = newCap + 1#64 ∧ s0.sp = sp ∧
             size ≤ newCap ∧ newCap < 0x1000#64⌝ ∗
             pool ∗ (base ↦₆₄ oldCap) ∗ memRegion (sp - 64#64) 64
         post := fun (size, oldCap, _newCap, sp) _s0 sf =>
           let nextUsed := oldCap + size
           pool ∗ memRegion (sp - 64#64) 64 ∗
             (if sf.readReg64 .x0 = 0 then
               (base ↦₆₄ oldCap)
              else
               (sf.readReg64 .x0 ↦₆₄ size) ∗ (base ↦₆₄ nextUsed)) } :
        Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)) :=
  rfl

/-- Polymorphic `{α : Type}` + `(ctx ...)` + shared `let` in `pre` and `post`. -/
rust_spec testPolyDecodeSpec {α : Type} (ctx encodeFn : α → List (BitVec 8))
    (bufPtr : ptr) (_ : usize := BitVec.ofNat 64 enc.length) (ghost val : α) : u64
  let enc := encodeFn val
  requires_cond bufPtr ≠ 0#64
  preserves     (bufPtr ↦ₛ enc)
  returns       1#64

/-- A single ABI parameter named `ctx` (`(ctx : ptr)`) is treated as a register argument (`x0 = ctx`),
    not as an empty outer context prefix. -/
c_spec testSingleArgNamedCtx (ctx : ptr) (ghost v : u64) : u64
  preserves (ctx ↦₆₄ v)
  returns   v

/--
error: duplicate struct-backed '[var : Type]' binder in specification header
-/
#guard_msgs in
c_spec testDuplicateStructBinder [a : BumpPairArgs] [b : BumpPairArgs] : u64
  returns 0#64

end HighLevelSpecTests

/-! ## Read-Only Points-To (`↦ᵣ`), `wp_sep_access_fast`, and `wp_simp_pre` / `wp_conv_pre` -/

section ReadOnlyAndWpPreTacticsTests

/-- Duplicability of read-only points-to atoms (`(a ↦₆₄ᵣ x) ∗ (a ↦₆₄ᵣ x) = (a ↦₆₄ᵣ x)` and `↦ᵣ`). -/
example (h : m ⊨ (a ↦₆₄ᵣ x) ∗ R) : m ⊨ (a ↦₆₄ᵣ x) ∗ (a ↦₆₄ᵣ x) ∗ R := by
  simpa only [← sepConj_assoc, pointsTo64RO_dup] using h

example (bs : List (BitVec 8)) (h : m ⊨ (a ↦ᵣ bs) ∗ R) :
    m ⊨ (a ↦ᵣ bs) ∗ (a ↦ᵣ bs) ∗ R := by
  simpa only [← sepConj_assoc, pointsToBytesRO_dup] using h

/-- Weakening writable `↦₆₄` / `↦ₛ` ownership to read-only `↦₆₄ᵣ` / `↦ᵣ`. -/
example (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ (a ↦₆₄ᵣ x) ∗ R :=
  Satisfies.pointsTo64_to_ro h

example (bs : List (BitVec 8)) (h : m ⊨ (a ↦ₛ bs) ∗ R) : m ⊨ (a ↦ᵣ bs) ∗ R :=
  Satisfies.pointsToBytes_to_ro h

/-- `SepLoad8`/`16`/`32`/`64` from read-only points-to atoms via `wp_sep_access` and `wp_sep_access_fast`. -/
example : SepLoad8 b ((a ↦₆₄ x) ∗ (b ↦₈ᵣ 7#8) ∗ R) 7#8 := by
  wp_sep_access_fast

example (v16 : BitVec 16) : SepLoad16 a (R ∗ (a ↦₁₆ᵣ v16) ∗ F) v16 := by
  wp_sep_access_fast

example (v32 : BitVec 32) : SepLoad32 a (R ∗ (a ↦₃₂ᵣ v32)) v32 := by
  wp_sep_access_fast

example : SepLoad64 a (R ∗ (a ↦₆₄ᵣ x) ∗ F) x := by
  wp_sep_access_fast

/-- Sub-slice byte load (`SepLoad8`) from a 32-bit read-only word `(a ↦₃₂ᵣ v)`. -/
example (v32 : BitVec 32) :
    SepLoad8 (a + 2#64) (R ∗ (a ↦₃₂ᵣ v32)) (v32.extractLsb' 16 8) := by
  wp_sep_access_fast

/-- Loads of 8, 16, 32, and 64-bit values from a concrete `.rodata` byte slice `a ↦ᵣ bs`. -/
def sampleRoBytes : List (BitVec 8) :=
  [0x01#8, 0x02#8, 0x03#8, 0x04#8, 0x05#8, 0x06#8, 0x07#8, 0x08#8,
   0x11#8, 0x22#8, 0x33#8, 0x44#8]

example : SepLoad8 (a + 3#64) (R ∗ (a ↦ᵣ sampleRoBytes)) 0x04#8 := by
  wp_sep_access_fast

example : SepLoad16 (a + 2#64) (R ∗ (a ↦ᵣ sampleRoBytes)) 0x0403#16 := by
  wp_sep_access_fast

example : SepLoad32 (a + 8#64) (R ∗ (a ↦ᵣ sampleRoBytes)) 0x44332211#32 := by
  wp_sep_access_fast

example : SepLoad64 a ((a ↦ᵣ sampleRoBytes) ∗ R) 0x0807060504030201#64 := by
  wp_sep_access_fast

/-- Steps `LDR` and `LDRB` from read-only `.rodata` (`↦ᵣ`), writes to a writable destination cell
    (`↦₆₄`), and unfolds `roPreAlias` only in the precondition via `wp_simp_pre`. -/
@[simp, arm64_norm] def ro_copy_addr : BitVec 64 := 0x10800#64

/-- `ro_copy_fn`:
    `ldr x8, [x1]; ldrb w9, [x1, #8]; add x8, x8, x9; str x8, [x0]; ret`. -/
def roCopyCode : FnCode :=
  .atAddr "ro_copy_fn" ro_copy_addr
    ("f9400028 " ++ -- 0x10800: ldr x8, [x1]
     "39402029 " ++ -- 0x10804: ldrb w9, [x1, #8]
     "8b090108 " ++ -- 0x10808: add x8, x8, x9
     "f9000008 " ++ -- 0x1080c: str x8, [x0]
     "d65f03c0")    -- 0x10810: ret

abbrev RoCopyCodeAt (prog : Program) : Prop :=
  roCopyCode.holds prog

def roPostTag (v : BitVec 64) : BitVec 64 := v + 0x11#64

def roPreAlias (dst roBase : BitVec 64) (old : BitVec 64) : SepProp :=
  (dst ↦₆₄ old) ∗ (roBase ↦ᵣ sampleRoBytes)

structure RoCopyArgs where
  dst    : BitVec 64
  roBase : BitVec 64
  old    : BitVec 64

def roCopySpec : Spec RoCopyArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.dst ∧ s0.readReg64 .x1 = a.roBase⌝ ∗
    roPreAlias a.dst a.roBase a.old
  post := fun a _ _ =>
    (a.dst ↦₆₄ roPostTag 0x0807060504030201#64) ∗
    (a.roBase ↦ᵣ sampleRoBytes)

theorem ro_copy_ok (prog : Program) (h_code : RoCopyCodeAt prog) :
    prog.subroutineOk "ro_copy_fn" roCopySpec := by
  wp_init a s0
  wp_simp_pre [roPreAlias]
  wp_steps
  unfold roPostTag
  wp_done

end ReadOnlyAndWpPreTacticsTests

section Stage3ToolingRegressionTests

/-! ## 32-Bit `CBZ` Branch Resolution, `.MI`/`.PL` Flags, and Points-To Splitting -/

@[simp, arm64_norm] def branch_w32_addr : BitVec 64 := 0x10900#64

/-- `branch_w32_fn`:
    `34000060` = `cbz w0, 0x1090c`
    `d2800020` = `mov x0, #1`
    `d65f03c0` = `ret`
    `d2800040` = `mov x0, #2`
    `d65f03c0` = `ret` -/
def branchW32Code : FnCode :=
  .atAddr "branch_w32_fn" branch_w32_addr
    ("34000060 " ++
     "d2800020 " ++
     "d65f03c0 " ++
     "d2800040 " ++
     "d65f03c0")

abbrev BranchW32CodeAt (prog : Program) : Prop :=
  branchW32Code.holds prog

abbrev branchW32NeZeroSpec : Spec (BitVec 32) where
  pre  := fun w s0 => ⌜s0.readReg64 .x0 = w.zeroExtend 64 ∧ w ≠ 0#32⌝
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64⌝

set_option maxHeartbeats 40000 in
theorem branch_w32_ne_zero_ok (prog : Program) (h_code : BranchW32CodeAt prog) :
    prog.subroutineOk "branch_w32_fn" branchW32NeZeroSpec := by
  wp_init w s0
  wp_steps
  wp_done

abbrev branchW32BeqFalseSpec : Spec (BitVec 32) where
  pre  := fun w s0 => ⌜s0.readReg64 .x0 = w.zeroExtend 64 ∧ (w == 0#32) = false⌝
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64⌝

set_option maxHeartbeats 40000 in
theorem branch_w32_beq_false_ok (prog : Program) (h_code : BranchW32CodeAt prog) :
    prog.subroutineOk "branch_w32_fn" branchW32BeqFalseSpec := by
  wp_init w s0
  wp_steps
  wp_done

abbrev branchW32UnresolvedSpec : Spec (BitVec 32) where
  pre  := fun w s0 => ⌜s0.readReg64 .x0 = w.zeroExtend 64⌝
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64 ∨ sf.readReg64 .x0 = 2#64⌝

/--
info: wp_steps: stopped at pc
-/
#guard_msgs (info, substring := true) in
set_option proofLib.wpVerbose true in
set_option maxHeartbeats 40000 in
theorem branch_w32_unresolved_ok (prog : Program) (h_code : BranchW32CodeAt prog) :
    prog.subroutineOk "branch_w32_fn" branchW32UnresolvedSpec := by
  wp_init w s0
  wp_steps
  wp_if h_z
  · wp_steps; wp_done
  · wp_steps; wp_done

/--
error: wp_step: current PC is an unresolved conditional branch:
  condition: (v == 0#64) = true
  then PC:   67084#64
  else PC:   67076#64
hint: split with `wp_if hcond` (if both branches are reachable) or prove `have hcond : (v == 0#64) =
  true := by bv_omega` (or `= false`) before stepping (or `wp_simp_pre [hcond]`)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 40000 in
example (prog : Program) (h_code : BranchFnCodeAt prog) :
    prog.subroutineOk "branch_fn" branchFnUnresolvedSpec := by
  wp_init v s0
  wp_step
  wp_step

/--
error: wp_step: could not fetch/decode instruction at PC `s0.pc`
hint: check (1) the `*Fns.lean` / `*Code.lean` decode module is imported or a `hasWords` / `hasCode` / `code_fetches` hypothesis is in context, (2) the PC offset is normalized (e.g. `entry + <off>#64`; try `wp_simp_pre` or `examples_generalize_entry`), or (3) execution did not step past function exit or into an un-inlined `BL` callee
-/
#guard_msgs (error, drop info) in
example (prog : Program) (s0 : State) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (fun _ _ => True) := by
  wp_step

/--
error: wp_focus_close (after running `skip`): unsolved side goal:
  prog.fetch pc = some inst
hint: instruction fetch side goal failed; ensure the function's `*Fns.lean` / `*Code.lean` decode theorem is imported/in scope and the PC offset is normalized
-/
#guard_msgs (error, drop info) in
example (prog : Program) (pc : BitVec 64) (inst : Instr) : prog.fetch pc = some inst := by
  wp_focus_close skip

/--
error: wp_focus_close (after running `skip`): unsolved side goal:
  a = b
hint: address/value equality side goal was not closed by `skip`; simplify or prove `a = b` before stepping
-/
#guard_msgs (error, drop info) in
example (a b : BitVec 64) : a = b := by
  wp_focus_close skip

/--
error: wp_step: no step rule succeeded for instruction `Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 1#5)
  (AddrMode.Offset (Reg.gpr 0#5)
    0#64)` (full: `Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 1#5)
  (AddrMode.Offset (Reg.gpr 0#5) 0#64)`) at PC `prog.fnAddr "bump_cell"`
effective address: `p`
spatial context points-to atoms: (p + 64#64) ↦₆₄ 0#64
(detail: wp_sep_access: no cell at p in
  (p + 64#64) ↦₆₄ 0#64)
hint: if the target cell is in context at a different width (`↦₆₄` vs `↦₈`/`↦₁₆`/`↦₃₂`) or inside a byte slice/region (`↦ₛ`, `↦ᵣ`, `memRegion`, `stackFrameAt`), prove the slice length bound (`off + w ≤ bs.length` for `wp_sep_access`), split the cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), or use `wp_sym_steps`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (h_code : BumpCellCodeAt prog) :
    prog.subroutineOk "bump_cell" {
      pre  := fun (p : BitVec 64) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ ((p + 64#64) ↦₆₄ 0#64)
      post := fun _ _ _ => emp
    } := by
  wp_init p s0
  wp_step

example (x y : BitVec 32) :
    ConditionHolds .MI (subsPState32 x y) = (x - y).msb ∧
    ConditionHolds .PL (subsPState32 x y) = !(x - y).msb ∧
    x.ult x = false ∧ x.slt x = false ∧ x.sle x = true := by
  simp only [conditionHolds_mi_subsPState32, conditionHolds_pl_subsPState32,
    bitvec_ult_self, bitvec_slt_self, bitvec_sle_self, and_self]

example (prog : Program) (target_pc : BitVec 64) (s : State) (lo hi : BitVec 32) (mid : BitVec 64)
    (post : State → SepProp → Prop)
    (h : SepWP prog target_pc s (((s.sp - 16#64) ↦₆₄ (hi ++ lo)) ∗ ((s.sp - 8#64) ↦₆₄ mid)) post) :
    SepWP prog target_pc s (((s.sp - 16#64) ↦₃₂ lo) ∗ ((s.sp - 8#64) ↦₆₄ mid) ∗ ((s.sp - 12#64) ↦₃₂ hi)) post := by
  apply (SepWP.combine_pointsTo32_sub s.sp 16#64 12#64)
  exact h

example (a : BitVec 64) (b0 b1 : BitVec 8) (lo hi : BitVec 32) (ws1 ws2 : List (BitVec 64)) (k1 k2 : Nat) :
    ((a ↦ₛ [b0]) = (a ↦₈ b0)) ∧
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) = (a ↦₁₆ (b1 ++ b0))) ∧
    ((a ↦₆₄* (ws1 ++ ws2)) = (a ↦₆₄* ws1) ∗ ((a + BitVec.ofNat 64 (8 * ws1.length)) ↦₆₄* ws2)) ∧
    (cells a (k1 + k2) = (cells a k1 ∗ cells (a + BitVec.ofNat 64 (8 * k1)) k2)) ∧
    ((pack32Pair lo hi).truncate 32 = lo) ∧
    (((pack32Pair lo hi) >>> 32).truncate 32 = hi) ∧
    (BitVec.ofNat 64 (countLeadingZeros a) = a.clz) := by
  refine ⟨pointsToBytes_singleton a b0, pointsTo8_pair a b0 b1, pointsToWords64_append a ws1 ws2,
    cells_split a k1 k2, ?_, ?_, ?_⟩ <;> simp

example (P Q R : SepProp) : (P ∗ Q) ∗ R = R ∗ (Q ∗ P) := by
  ac_rfl

/--
error: Tactic `rfl` failed
-/
#guard_msgs (error, substring := true) in
example (P Q R : SepProp) : P ∗ Q = P ∗ R := by
  ac_rfl

end Stage3ToolingRegressionTests

/-! ## `SepProp.eq_of_entails`, `ISepProp` (`⌈P⌉ᵢ`), and Freeze Updates -/

section BasicSepPropTests

/-- Bi-entailment equality on `SepProp` (`SepProp.eq_of_entails`). -/
example (a b : BitVec 64) (x y : BitVec 64) :
    ((a ↦₆₄ x) ∗ (b ↦₆₄ y)) = ((b ↦₆₄ y) ∗ (a ↦₆₄ x)) :=
  SepProp.eq_of_entails (by sep_entail) (by sep_entail)

/-- `ISepProp` monoidal embedding (`⌈·⌉ᵢ`) and `satisfies_ofSepProp_iff` equivalence. -/
example (m : Memory) (a : BitVec 64) (v : BitVec 8) (hm : m ⊨ (a ↦₈ᵣ v)) :
    (⌈a ↦₈ᵣ v⌉ᵢ).Satisfies m :=
  (ISepProp.satisfies_ofSepProp_iff _ m).mpr hm

/-- Frame-preserving freeze updates (`|==>`) in `SepProp` (`pointsTo64_freeze_ro`)
    and `Satisfies.of_bupd_frame_left`. -/
example (m : Memory) (a : BitVec 64) (v : BitVec 64) (R : SepProp)
    (hm : m ⊨ (a ↦₆₄ v) ∗ R) : m ⊨ ((a ↦₆₄ᵣ v) ∗ (a ↦₆₄ᵣ v)) ∗ R := by
  have hm_ro : m ⊨ (a ↦₆₄ᵣ v) ∗ R :=
    Satisfies.of_bupd_frame_left (pointsTo64_freeze_ro a v) hm
  rwa [← pointsTo64RO_dup a v] at hm_ro

end BasicSepPropTests

/-! ## Code-Derived and Symbol-Relative Cut Points on `CodeTree` / `FnCode` -/

section NamedCutPointsTests

def bumpPairCodeTree : CodeTree :=
  ProgramReflection.WordTree.ofWords bumpPairCode.hex

#guard_expr (code_call_off% bumpPairCodeTree bump_pair_addr bump_cell_addr) =ₛ 8#64
#guard_expr (code_call_off% bumpPairCodeTree bump_pair_addr bump_cell_addr 1) =ₛ 16#64
#guard_expr (code_call_off% bumpPairCode "bump_pair" bump_cell_addr 0) =ₛ 8#64
#guard_expr (code_call_off% bumpPairCode "bump_pair" bump_cell_addr 1) =ₛ 16#64
#guard_expr (words_ret_off% bumpPairCodeTree) =ₛ 24#64

example : code_call_addr% bumpPairCodeTree bump_pair_addr bump_cell_addr 0 =
    bump_pair_addr + 8#64 := rfl
example : code_call_addr% bumpPairCodeTree bump_pair_addr bump_cell_addr 1 =
    bump_pair_addr + 16#64 := rfl
example : Obj.findBlOff bumpPairCodeTree bump_pair_addr bump_cell_addr 0 = 8#64 := rfl
example : Obj.findBlOff bumpPairCodeTree bump_pair_addr bump_cell_addr 1 = 16#64 := rfl
example : Obj.findRetOff bumpPairCodeTree 0 = 24#64 := rfl

/-- Multi-segment `SepWP` proof of `bump_pair` with segment boundaries and step counts derived from
    `bumpPairCodeTree` (`wp_cut_call`, `code_call_off%`, `wp_steps_to_call`, `wp_steps_to_ret`). -/
theorem bump_pair_named_cuts_ok (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellCSpec) :
    prog.subroutineOk "bump_pair" bumpPairCSpec := by
  wp_init a s0
  wp_cut_call bumpPairCodeTree bump_pair_addr bump_cell_addr 0
  wp_steps_to_call bumpPairCodeTree bump_pair_addr bump_cell_addr 0
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  apply SepWP.cut (mid := bump_pair_addr + code_call_off% bumpPairCodeTree bump_pair_addr bump_cell_addr 1)
  wp_step
  wp_call h_bump
  wp_steps_to_call bumpPairCodeTree bump_pair_addr bump_cell_addr 1
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  wp_step
  wp_call h_bump
  wp_steps_to_ret bumpPairCodeTree
  wp_step
  wp_done

/-- Multi-segment `SepWPp` proof of `bump_pair` using `wpp_init`, `sepWPp_cut_call`,
    `code_call_off%`, `wp_steps_to_call`, and `wp_steps_to_ret`. -/
theorem bump_pair_sepWPp_named_cuts_ok (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellCSpec) :
    prog.subroutineOk "bump_pair"
      { pre := fun (a : BumpPairArgs) s0 =>
          ⌜s0.readReg64 .x0 = a.p ∧ s0.readReg64 .x1 = a.q⌝ ∗
          (a.p ↦₆₄ a.v) ∗ (a.q ↦₆₄ a.w) ∗ stackFrameAt s0.sp 16
        post := fun a _ sf =>
          (a.p ↦₆₄ (a.v + 1#64)) ∗ (a.q ↦₆₄ (a.w + 1#64)) ∗ stackFrameAt sf.sp 16 } := by
  wpp_init a s0
  sepWPp_cut_call bumpPairCodeTree bump_pair_addr bump_cell_addr 0
  wp_steps_to_call bumpPairCodeTree bump_pair_addr bump_cell_addr 0
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  apply SepWPp.of_sepWP (mid := bump_pair_addr + code_call_off% bumpPairCodeTree bump_pair_addr bump_cell_addr 1)
  wp_step
  wp_call h_bump
  wp_steps_to_call bumpPairCodeTree bump_pair_addr bump_cell_addr 1
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  apply SepWPp.of_sepWP_ret
  wp_step
  wp_call h_bump
  wp_steps_to_ret bumpPairCodeTree
  wp_step
  wp_done

end NamedCutPointsTests

/-! ## Panic-Aware (`wpp_call`) and Frozen (`wpp_call_frozen`, `Spec.inImage`) Call-Site Automation -/

section WppCallTests

/-- Panic-aware variant of `bumpCellSpec`: may panic with `⌜v = 0#64⌝ ∗ anyHeap` if `v = 0`,
    and on normal return guarantees `v ≠ 0#64` and `(p ↦₆₄ (v + 1#64))`. -/
def bumpCellPanicSpec : Spec (BitVec 64 × BitVec 64) :=
  Spec.allowPanicWhen
    { pre  := fun (p, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v)
      post := fun (p, v) _ _sf => ⌜v ≠ 0#64⌝ ∗ (p ↦₆₄ (v + 1#64)) }
    (fun (_, v) _ _ => v = 0#64)

/-- Panic-aware caller contract for `bump_pair` calling `bump_cell(p)` and `bump_cell(q)`:
    may panic if `v = 0#64 ∨ w = 0#64`. -/
def bumpPairPanicSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  Spec.allowPanicWhen
    { pre  := fun (p, q, v, w) s0 =>
        ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = q⌝ ∗
        (p ↦₆₄ v) ∗ (q ↦₆₄ w) ∗ stackFrame16 s0
      post := fun (p, q, v, w) _ sf =>
        ⌜v ≠ 0#64 ∧ w ≠ 0#64⌝ ∗
        (p ↦₆₄ (v + 1#64)) ∗ (q ↦₆₄ (w + 1#64)) ∗ stackFrame16 sf }
    (fun (_, _, v, w) _ _ => v = 0#64 ∨ w = 0#64)

/-- `wpp_call` on a `SepWPp` goal closes the preceding `SepWPp.of_sepWP` segment, infers `ret_pc`,
    the ghost argument `(p, v)`, and the spatial frame `T`, and discharges the panic obligation. -/
theorem bump_pair_wpp_call_ok (prog : Program) (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" bumpCellPanicSpec) :
    prog.subroutineOk "bump_pair" bumpPairPanicSpec := by
  wpp_init a s0
  apply SepWPp.of_sepWP
  wp_steps
  wpp_call h_bump
  apply SepWPp.of_sepWP
  wp_steps
  wp_call h_bump (x := (a.2.1, a.2.2.2)) (on_panic := fun hv => Or.inr hv)
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/-- Frozen (`Spec.inImage img`) caller and callee test: `wpp_call` and `wpp_call_frozen`
    automatically discharge `img.FrozenLoaded s` and `s.symtab = img.symtab` across the call
    and re-introduce `img.FrozenLoaded sf` and `sf.symtab = img.symtab` in the post-call state,
    without any `(ret_pc := ...)` or `(T := ...)` annotations. -/
theorem bump_pair_wpp_call_frozen_ok (img : Obj.Image) (prog : Program)
    (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" (bumpCellPanicSpec.inImage img)) :
    prog.subroutineOk "bump_pair" (bumpPairPanicSpec.inImage img) := by
  wpp_init a s0
  apply SepWPp.of_sepWP_frozen ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  wp_steps
  wpp_call_frozen h_bump
  apply SepWPp.of_sepWP_frozen hfz_sf hsym_sf
  wp_steps
  wpp_call h_bump
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/-- `SepWP.of_sepWP_frozen` + `wp_call` on a `Spec.inImage img` contract in ordinary `SepWP`:
    preserves `img.FrozenLoaded` and `symtab = img.symtab` across both calls. -/
theorem bump_pair_wp_call_frozen_ok (img : Obj.Image) (prog : Program)
    (h_code : BumpPairCodeAt prog)
    (h_addr : prog.fnAddr "bump_cell" = bump_cell_addr)
    (h_bump : prog.subroutineOk "bump_cell" (bumpCellSpec.inImage img)) :
    prog.subroutineOk "bump_pair" (bumpPairSpec.inImage img) := by
  wp_init a s0
  apply SepWP.of_sepWP_frozen ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  wp_steps
  wp_call h_bump
  apply SepWP.of_sepWP_frozen hfz_sf hsym_sf
  wp_steps
  wp_call h_bump
  wp_steps
  wp_done

/-- Always-panicking helper (`post := ⌜False⌝`): `wpp_call` automatically closes the post-call
    continuation via `False.elim` without needing a separate continuation proof. -/
def alwaysPanicsCellSpec : Spec (BitVec 64 × BitVec 64) :=
  Spec.allowPanicWhen
    { pre  := fun (p, v) s0 => ⌜s0.readReg64 .x0 = p ∧ v = 0#64⌝ ∗ (p ↦₆₄ v)
      post := fun _ _ _ => ⌜False⌝ }
    (fun (_, v) _ _ => v = 0#64)

example (prog : Program) (ret : BitVec 64) (s : State) (p : BitVec 64) (R : SepProp)
    (h_pc : s.pc = bump_cell_addr)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_x0 : s.readReg64 .x0 = p)
    (h_callee : subroutine_ok prog bump_cell_addr alwaysPanicsCellSpec) :
    SepWPp prog ret s (p ↦₆₄ 0#64)
      (fun _ _ => False)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜0#64 = 0#64⌝ ∗ anyHeap) ∗ R)) := by
  wpp_call h_callee

end WppCallTests

/-! ## `clock_gettime` Oracle `SepWP` Step Lemmas -/

section ClockGettimeTests

/-- `SepWP.step_svc_clock_gettime` steps across `SVC #0` (`X8 = 113`, `W0 ≤ 7`) under
    `Syscall.time`, exposing `ts := s.oracle.clockGettime s.oracleIdx`, `ts.nsec.val < 1_000_000_000`,
    and `s'.oracleIdx = s.oracleIdx + 1`. -/
example (prog : Program) (hsvc : prog.svc = Syscall.time) (pc : BitVec 64) (s : State) (tp : BitVec 64)
    (bs₀ : List (BitVec 8)) (F : SepProp)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 113#64)
    (hclk : (s.readReg32 .x0).toNat ≤ 7)
    (htp : s.readReg64 .x1 = tp)
    (hlen : bs₀.length = 16) :
    SepWP prog (pc + 4#64) s ((tp ↦ₛ bs₀) ∗ F)
      (fun sf P =>
        let ts := s.oracle.clockGettime s.oracleIdx
        sf.readReg64 .x0 = 0#64 ∧
        sf.oracleIdx = s.oracleIdx + 1 ∧
        ts.nsec.val < 1000000000 ∧
        (BitVec.ofNat 64 ts.nsec.val).toNat < 1000000000 ∧
        P = (((tp ↦₆₄ ts.sec) ∗ ((tp + 8#64) ↦₆₄ BitVec.ofNat 64 ts.nsec.val)) ∗ F))
      (fun _ => ⌜False⌝) := by
  refine SepWP.step_svc_clock_gettime hpc hrun hfetch hx8 hclk htp hlen fun hlt => ?_
  apply SepWP.done (by rfl) (by simpa using hrun)
  refine ⟨rfl, rfl, hlt, Timespec.toNat_nsec_ofNat_lt _, ?_⟩
  rw [pointsToBytes_encodeTimespec]

/-- Two consecutive `SVC #0` `clock_gettime` calls with `SepWP.step_svc_clock_gettime_words`
    consume independent oracle entries (`s.oracleIdx` and `s.oracleIdx + 1`). -/
example (prog : Program) (hsvc : prog.svc = Syscall.time) (pc : BitVec 64) (s : State) (tp : BitVec 64)
    (sec₀ nsec₀ : BitVec 64) (F : SepProp)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.system false 0#16))
    (hf1 : prog.fetch (pc + 4#64) = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 113#64)
    (htp : s.readReg64 .x1 = tp) :
    SepWP prog (pc + 8#64) (s.writeReg64 .x0 1#64)
      (((tp ↦₆₄ sec₀) ∗ ((tp + 8#64) ↦₆₄ nsec₀)) ∗ F)
      (fun sf P =>
        let ts1 := s.oracle.clockGettime (s.oracleIdx + 1)
        sf.readReg64 .x0 = 0#64 ∧
        sf.oracleIdx = s.oracleIdx + 2 ∧
        ts1.nsec.val < 1000000000 ∧
        P = (((tp ↦₆₄ ts1.sec) ∗ ((tp + 8#64) ↦₆₄ BitVec.ofNat 64 ts1.nsec.val)) ∗ F))
      (fun _ => ⌜False⌝) := by
  refine SepWP.step_svc_clock_gettime_words
    (by simpa using hpc) (by simpa using hrun) hf0 (by simpa using hx8) (by simp [State.readReg32])
    (by simpa using htp) fun _hlt0 => ?_
  refine SepWP.step_svc_clock_gettime_words
    rfl (by simpa using hrun) hf1 (by simpa using hx8) (by simp [State.readReg32])
    (by simpa using htp) fun hlt1 => ?_
  have hpc8 : (pc + 4#64) + 4#64 = pc + 8#64 := by bv_arith
  apply SepWP.done hpc8 (by simpa using hrun)
  exact ⟨rfl, by simp [State.nextOracle], hlt1, rfl⟩

/--
error: unsolved goals
m : Memory
a b c x y z : BitVec 64
R F✝ : SepProp
prog : Program
hsvc : prog.svc = Syscall.time
pc : BitVec 64
s : State
tp sec₀ nsec₀ : BitVec 64
F : SepProp
hpc : s.pc = pc
hrun : s.status = ExecStatus.Running
hf0 : prog.fetch pc = some (Instr.system false 0#16)
hx8 : s.readReg64 Reg.x8 = 113#64
htp : s.readReg64 Reg.x1 = tp
⊢ False
-/
#guard_msgs in
example (prog : Program) (hsvc : prog.svc = Syscall.time) (pc : BitVec 64) (s : State) (tp : BitVec 64)
    (sec₀ nsec₀ : BitVec 64) (F : SepProp)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 113#64)
    (htp : s.readReg64 .x1 = tp) :
    SepWP prog (pc + 4#64) (s.writeReg64 .x0 8#64)
      (((tp ↦₆₄ sec₀) ∗ ((tp + 8#64) ↦₆₄ nsec₀)) ∗ F)
      (fun _ _ => True) (fun _ => ⌜False⌝) := by
  refine SepWP.step_svc_clock_gettime_words
    (by simpa using hpc) (by simpa using hrun) hf0 (by simpa using hx8)
    (by simp [State.readReg32])
    (by simpa using htp) fun _ => ?_
  apply SepWP.done (by rfl) (by simpa using hrun) trivial

end ClockGettimeTests

/-! ## Diagnostic Error Message Regression Tests (`wp_call` and `wp_done`) -/

section DiagnosticErrorTests

/-- Wrapper around `CalleeSavedPreserved` used to test the `wp_done` callee-saved hint. -/
def CustomCalleeSaved (s0 sf : State) : Prop :=
  CalleeSavedPreserved s0 sf

/--
error: wp_done: current PC `66324#64` does not match target PC `s0.readReg64 Reg.lr`
hint: execution is stopped at call instruction `Instr.bl (-20#64)` at `0x10314#64`; use `wp_call <callee_spec>` before `wp_done`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : LdrswHiCallerCodeAt prog) (s0 : State)
    (hpc : s0.pc = 0x10314#64) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (fun _ _ => True) := by
  wp_done

/--
error: wp_done: current PC `66564#64` does not match target PC `66568#64`
hint: `RET` (`Instr.ret (Reg.gpr 30#5)`) at `0x10404#64` was not stepped; check that `x30`/`lr` is restored and `status = .Running`, or run `wp_step`; 1 step(s) (4 bytes) remaining before target PC (-4 bytes) (run `wp_steps` or `wp_steps 1`)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : RetConstCodeAt prog) (s0 : State)
    (hpc : s0.pc = ret_const_addr) (hrun : s0.status = .Running) :
    SepWP prog 0x10408#64 s0 emp (fun _ _ => True) := by
  wp_steps 1
  wp_done

/--
error: wp_done: current PC `65536#64` does not match target PC `s0.readReg64 Reg.lr`
hint: `wp_steps` stopped early at `Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 1#5) (AddrMode.Offset (Reg.gpr 0#5) 0#64)` at `0x10000#64` due to a missing spatial points-to atom or slice bound (run `wp_step` to see the stuck load/store)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : BumpCellCodeAt prog) (s0 : State)
    (hpc : s0.pc = bump_cell_addr) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (fun _ _ => True) := by
  wp_steps
  wp_done

/--
error: wp_done: current PC `base + 88#64` does not match target PC `base + 84#64`
hint: stepped 4 bytes past target PC (+4 bytes); use `wp_steps_to_insn` or normalize `target_pc` offsets
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 88#64) (hrun : s.status = .Running) :
    SepWP prog (base + 84#64) s emp (fun _ _ => True) := by
  wp_done

/--
error: wp_done: current PC `base + 88#64` does not match target PC `s.readReg64 Reg.x1`
hint: run `wp_step` to see why execution stopped at `base + 0x58#64`, or run `wp_steps` before `wp_done`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (base : BitVec 64) :
    ∀ s : State, s.pc = base + 88#64 → s.status = .Running →
      SepWP prog (s.readReg64 .x1) s emp (fun _ _ => True) := by
  intro s hpc hrun
  wp_done

/--
error: wp_done: postcondition value mismatch:
  actual:   sf.readReg64 (Reg.gpr 19#5)
  expected: s0.readReg64 (Reg.gpr 19#5)
hint: destructure local callee-saved hypothesis `hcc` (e.g. `rcases hcc with ⟨...⟩`) before `wp_done`
-/
#guard_msgs (error, drop info) in
set_option proofLib.wpDoneAutoDisjAndCalleeSaved false in
set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s0 sf : State)
    (hpc : sf.pc = pc) (hrun : sf.status = .Running)
    (hcc : CustomCalleeSaved s0 sf) :
    SepWP prog pc sf emp (fun st _ => st.readReg64 .x19 = s0.readReg64 .x19) := by
  wp_done

set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s0 sf : State)
    (hpc : sf.pc = pc) (hrun : sf.status = .Running)
    (hcc : CustomCalleeSaved s0 sf) :
    SepWP prog pc sf emp (fun st _ => st.readReg64 .x19 = s0.readReg64 .x19) := by
  wp_done

/--
error: wp_done: postcondition value mismatch:
  actual:   if c = true then 1#64 else 2#64
  expected: 1#64
hint: actual value contains an unreduced conditional or width cast; use `wp_by_cases hc : <cond>` or `simp only [wp_norm, width_norm]` before `wp_done`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s : State) (c : Bool)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = if c then 1#64 else 2#64) :
    SepWP prog pc s emp (fun st _ => st.readReg64 .x0 = 1#64) := by
  wp_done

/--
error: wp_call: failed to prove 16-byte stack pointer alignment (`s.spAligned = true`):
  s.spAligned = true
hint: offset 32 is 16-byte aligned, so initial alignment `hsp : s0.spAligned = true` (or `(s0.sp &&& 15#64 == 0#64) = true`) is likely missing from local hypotheses / loop invariant
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s0 s : State)
    (h_pc : s.pc = entry) (h_run : s.status = .Running)
    (h_sp : s.sp = s0.sp - 32#64) (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ _ => True) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun _ _ => True) := by
  wp_call h_callee ()

/--
error: wp_call: failed to prove 16-byte stack pointer alignment (`s.spAligned = true`):
  s.spAligned = true
hint: stack offset 24 is not a multiple of 16
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s0 s : State)
    (h_pc : s.pc = entry) (h_run : s.status = .Running)
    (h_sp0 : s0.spAligned = true)
    (h_sp : s.sp = s0.sp - 24#64) (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ _ => True) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun _ _ => True) := by
  wp_call h_callee ()

/--
error: wp_call: failed to prove callee precondition conjunct: (conjunct 2/3)
  p.toNat + 16 < 1000
normalized:
  p.toNat + 16 < 1000
with unified ghost(s): ghost := p, ghost := (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
  (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)
hint: prove `have h_pre : p.toNat + 16 <
  1000 := by ...` before `wp_call`; if ghost variables are underdetermined, pass them explicitly with `wp_call h_callee <ghost_arg>`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 35000 in
example (prog : Program) (h_code : LdrswHiCallerCodeAt prog)
    (h_addr : prog.fnAddr "ldrsw_hi_callee" = ldrsw_hi_callee_addr)
    (h_callee : prog.subroutineOk "ldrsw_hi_callee" boundedCalleeSpec) :
    prog.subroutineOk "ldrsw_hi_caller" {
      pre  := fun (p : BitVec 64) s0 =>
        ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ 0#64) ∗ stackFrame16 s0
      post := fun _ _ _ => emp
    } := by
  wp_init p s0
  wp_steps
  wp_call h_callee

def elfSymTestProg : Program :=
  { base := 0x20000#64
    code := []
    symbols := [("alpha_fn", 0x100), ("beta_fn", 0x200)] }

/--
error: wp_call: call target address does not match callee entry: h_beta is the wrong contract (expected entry 0x20100#64 ("alpha_fn") / got 0x20200#64 ("beta_fn"))
  call target PC: 0x20100#64 (symbol: "alpha_fn" at 0x20100)
  callee entry:   0x20200#64 (symbol: "beta_fn" at 0x20200)
  raw target PC:  131328#64
  raw callee:     131584#64
hint: ensure execution has stepped to the `BL` call site (`wp_steps` / `wp_sym_steps`) and pass the contract matching the call target PC
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = 0x20100#64) (h_run : s.status = .Running)
    (h_sp : s.spAligned = true) (h_lr : s.readReg64 .lr = ret_pc)
    (h_beta : subroutine_ok elfSymTestProg 0x20200#64
      (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ _ => True) (fun _ => emp))) :
    SepWP elfSymTestProg ret_pc s emp (fun _ _ => True) := by
  wp_call h_beta ()

/--
error: wp_call: call target address does not match callee entry: callee entry is an unresolved metavariable (?m.51); instantiate or pass the callee entry address explicitly
  call target PC: 0x20100#64 (symbol: "alpha_fn" at 0x20100)
  callee entry:   ?m.51 (unresolved metavariable)
  raw target PC:  131328#64
  raw callee:     ?m.51
hint: the callee contract's entry address contains an unresolved metavariable (`?m.51`); pass the entry address argument explicitly to `h_poly` (e.g. `wp_call (h_poly <entry_addr>)`) or supply a local `prog.fnAddr "<callee>" = ...` / `Obj.Loads` hypothesis
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (ret_pc base : BitVec 64) (s : State)
    (h_pc : s.pc = 0x20100#64) (h_run : s.status = .Running)
    (h_sp : s.spAligned = true) (h_lr : s.readReg64 .lr = ret_pc)
    (h_poly : ∀ (off : BitVec 64), off ≠ 0#64 →
      subroutine_ok elfSymTestProg (base + off)
        (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
          (fun _ _ _ => True) (fun _ => emp))) :
    SepWP elfSymTestProg ret_pc s emp (fun _ _ => True) := by
  wp_call h_poly ()

/--
error: wp_done: heartbeat timeout during postcondition verification
  subgoal: SepWP prog target_pc (s.writeReg64 Reg.x0 (a + 1#64)) emp fun sf x => sf.readReg64 Reg.x0 = a + 2#64
hint: split or focus spatial containers with `wp_focus`, prove pure/address facts beforehand with `have h : ... := by bv_omega`, or compact a deep state with `wp_compact` before `wp_done`
-/
#guard_msgs (error, drop info) in
example (prog : Program) (target_pc a : BitVec 64) (s : State)
    (h_pc : (s.writeReg64 .x0 (a + 1#64)).pc = target_pc)
    (h_run : (s.writeReg64 .x0 (a + 1#64)).status = .Running) :
    SepWP prog target_pc (s.writeReg64 .x0 (a + 1#64)) emp
      (fun sf _ => (sf.readReg64 .x0 = a + 2#64)) := by
  set_option maxHeartbeats 1 in
  wp_done

/--
error: wp_steps: heartbeat timeout during extracting state and PC at step #1
  subgoal: SepWP prog (s0.readReg64 Reg.lr) s0 (s0.readReg64 Reg.x0 ↦₆₄ 0#64) fun sf x => sf.readReg64 Reg.x0 = 0#64
hint: split the stepping block into smaller chunks (`wp_steps <n>` / `wp_compact`), focus the accessed memory atom with `wp_focus`, or discharge a branch/address side condition beforehand with `have h : ... := by bv_omega`
-/
#guard_msgs (error, drop info) in
example (prog : Program) (s0 : State) (h_code : LdrswHiCalleeCodeAt prog)
    (h_pc : s0.pc = ldrsw_hi_callee_addr) (h_run : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 (s0.readReg64 .x0 ↦₆₄ 0#64)
      (fun sf _ => sf.readReg64 .x0 = 0#64) := by
  set_option maxHeartbeats 1 in
  wp_steps

/--
error: wp_norm_lhs: heartbeat timeout during LHS `wp_norm` / `arm64_norm` normalization
  subgoal: (s.writeReg64 Reg.x0 (a + 1#64)).readReg64 Reg.x1 = a
hint: isolate the equality subgoal (`wp_focus` / `have h : ... := by ...`) or compact a deep `State` update spine first with `wp_compact`
-/
#guard_msgs (error, drop info) in
example (s : State) (a : BitVec 64) :
    (s.writeReg64 .x0 (a + 1#64)).readReg64 .x1 = a := by
  set_option maxHeartbeats 1 in
  wp_norm_lhs

/--
error: wp_done: closed current goal, but 1 unfocused goal remains open:
  1. [case h] pure side condition (arithmetic bound):
     goal: ⊢ cur < 10
     try:  `omega` (or use `wp_done?` to keep residual goals open)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s : State) (cur : Nat)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWP prog pc s emp (fun _ _ => True) := by
  have _hbound : cur < 10 := ?h
  wp_done

/--
error: wp_done: closed current goal, but 1 unfocused goal remains open:
  1. [case hbv] pure side condition (BitVec bound):
     goal: ⊢ (x + 1#64).ult 10#64 = true
     try:  `bv_arith` (or `bv_omega`) (or use `wp_done?` to keep residual goals open)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (pc x : BitVec 64) (s : State)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWP prog pc s emp (fun _ _ => True) := by
  have _hbv : (x + 1#64).ult 10#64 = true := ?hbv
  wp_done

set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s : State) (cur : Nat) (hcur : cur < 5)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWP prog pc s emp (fun _ _ => True) := by
  have _hbound : cur < 10 := ?h
  wp_done?
  omega

set_option proofLib.wpDoneAllowResidualGoals true in
set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s : State) (cur : Nat) (hcur : cur < 5)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWP prog pc s emp (fun _ _ => True) := by
  have _hbound : cur < 10 := ?h
  wp_done
  omega

/--
error: wp_done: closed current goal, but 1 unfocused goal remains open:
  1. [case right] open SepWP execution goal:
     current PC: 0x10400#64 | target PC: s0.readReg64 Reg.lr (2 step(s) remaining to `RET`)
     try:  `wp_steps` (then `wp_done`) (or use `wp_done?` to keep residual goals open)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : RetConstCodeAt prog) (s0 s1 : State) (pc : BitVec 64)
    (hpc0 : s0.pc = ret_const_addr) (hrun0 : s0.status = .Running)
    (hpc1 : s1.pc = pc) (hrun1 : s1.status = .Running) :
    SepWP prog pc s1 emp (fun _ _ => True) ∧
      SepWP prog (s0.readReg64 .lr) s0 emp (fun _ _ => True) := by
  constructor
  wp_done

set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s : State)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWPp prog pc s emp (fun _ _ => True) (fun _ _ => True) := by
  wp_done

/--
error: wp_done: current PC `base + 72#64` does not match target PC `base + 84#64`
hint: 3 step(s) (12 bytes) remaining before target PC (-12 bytes); run `wp_steps` (or `wp_steps 3`) before `wp_done`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 72#64) (hrun : s.status = .Running) :
    SepWP prog (base + 84#64) s emp (fun _ _ => True) := by
  wp_done

/--
error: wp_done: current PC `66560#64` does not match target PC `s0.readReg64 Reg.lr`
hint: execution is stopped at `Instr.moveWide RegWidth.W64 MoveWideOp.MOVZ (Reg.gpr 0#5) (42#16) 0` at `0x10400#64` (2 step(s) remaining to `RET`); run `wp_steps` before `wp_done`
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : RetConstCodeAt prog) (s0 : State)
    (hpc : s0.pc = ret_const_addr) (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (fun _ _ => True) := by
  wp_done

/--
error: wp_done: closed current goal, but 1 unfocused goal remains open:
  1. [case helse (¬c = 0#64)] unresolved branch subgoal (open SepWP execution goal):
     current PC: 0x10400#64 | target PC: s0.readReg64 Reg.lr (2 step(s) remaining to `RET`)
     try:  focus each branch after `wp_if` / `by_cases` with `·`, then run `wp_steps` (then `wp_done`) (or use `wp_done?` to keep residual goals open)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : RetConstCodeAt prog) (s0 : State) (c : BitVec 64)
    (hpc : s0.pc = if c = 0#64 then s0.readReg64 .lr else ret_const_addr)
    (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (fun _ _ => True) := by
  wp_if hcond
  wp_done

/--
error: wp_done: closed current goal, but 1 unfocused goal remains open:
  1. [case neg (¬c = 0#64)] unresolved conditional branch (SepWP):
     condition: c = 0#64 | then PC: s0.readReg64 Reg.lr | else PC: 0x10400#64
     try:  focus each branch after `wp_if` / `by_cases` with `·`, then run `wp_if hcond` (or `wp_if_join <join_pc> <inv>`) (or use `wp_done?` to keep residual goals open)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : RetConstCodeAt prog) (s0 : State) (c : BitVec 64)
    (hpc : s0.pc = if c = 0#64 then s0.readReg64 .lr else ret_const_addr)
    (hrun : s0.status = .Running) :
    SepWP prog (s0.readReg64 .lr) s0 emp (fun _ _ => True) := by
  by_cases hcond : c = 0#64
  simp only [hcond, ↓reduceIte] at hpc
  wp_done

set_option maxHeartbeats 30000 in
example (prog : Program) (pc : BitVec 64) (s : State) (acc d : Nat)
    (hpc : (s.writeReg32 .x0 1#32).pc = pc)
    (hrun : (s.writeReg32 .x0 1#32).status = .Running) :
    SepWP prog pc (s.writeReg32 .x0 1#32) emp (fun st _ =>
      st.readReg32 .x0 =
        match match (pure (acc * 10 + d) : Option Nat) with
          | some x => some (BitVec.ofNat 64 x)
          | none => none with
        | some _ => 1#32
        | none => 0#32) := by
  wp_done

/--
error: wp_done: postcondition value mismatch:
  actual:   1#32
  expected: 2#32
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 30000 in
example (prog : Program) (pc : BitVec 64) (s : State) (acc d : Nat)
    (hpc : (s.writeReg32 .x0 1#32).pc = pc)
    (hrun : (s.writeReg32 .x0 1#32).status = .Running) :
    SepWP prog pc (s.writeReg32 .x0 1#32) emp (fun st _ =>
      st.readReg32 .x0 =
        match match (pure (acc * 10 + d) : Option Nat) with
          | some x => some (BitVec.ofNat 64 x)
          | none => none with
        | some _ => 2#32
        | none => 0#32) := by
  wp_done

set_option maxHeartbeats 30000 in
example (prog : Program) (pc p : BitVec 64) (s : State)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    ∃ v : BitVec 64, SepWP prog pc s (p ↦₆₄ 77#64) (sepPost (fun _ => True) (p ↦₆₄ v)) := by
  refine ⟨?_, ?_⟩
  rotate_left 1
  wp_done

/--
error: wp_done: closed current goal, but 1 unfocused goal remains open:
  1. [case refine_1] unassigned witness goal:
     goal: ⊢ BitVec 8
     try:  instantiate this witness explicitly (`exact <val>` / `use <val>`) (or use `wp_done?` to keep residual goals open)
-/
#guard_msgs (error, drop info) in
set_option maxHeartbeats 25000 in
example (prog : Program) (pc : BitVec 64) (s : State)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    ∃ _v : BitVec 8, SepWP prog pc s emp (fun _ _ => True) := by
  refine ⟨?_, ?_⟩
  rotate_left 1
  wp_done

/-! ### `wp_steps` Stop-Reason Diagnostics (`proofLib.wpVerbose`) -/

@[simp, arm64_norm] def stuck_svc_addr : BitVec 64 := 0x10950#64

def stuckSvcCode : FnCode :=
  .atAddr "stuck_svc" stuck_svc_addr
    ("d2800020 " ++ -- 0x10950: mov x0, #1
     "d4000001 " ++ -- 0x10954: svc #0
     "d65f03c0")    -- 0x10958: ret

abbrev stuckSvcSpec : Spec Unit where
  pre  := fun _ _s0 => emp
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64⌝

#guard_msgs in
set_option maxHeartbeats 40000 in
example (prog : Program) (h_code : BranchFnCodeAt prog) :
    prog.subroutineOk "branch_fn" branchFnUnresolvedSpec := by
  wp_init v s0
  wp_steps
  wp_if h_z
  · wp_steps; wp_done
  · wp_steps; wp_done

/--
info: wp_steps: stopped at pc 67924#64 (target s0.readReg64 Reg.lr): no step rule applies
wp_step: no step rule succeeded for instruction `Instr.system false 0#16` (full: `Instr.system false 0#16`) at PC `67924#64`
spatial context points-to atoms: (none)
(detail: wp_focus_close (after running `(first | wp_norm_lhs | wp_norm_goal)`): unsolved side goal:
  (evalSvc prog.svc ((s0.writeReg64 (Reg.gpr 0#5) 1#64).setPC 67924#64)).mem = s0.mem
hint: address/value equality side goal was not closed by `(first | wp_norm_lhs | wp_norm_goal)`; simplify or prove `(evalSvc prog.svc ((s0.writeReg64 (Reg.gpr 0#5) 1#64).setPC 67924#64)).mem = s0.mem` before stepping)
next: prove any missing side condition (e.g. `have h : ... := by bv_arith`), focus/split the accessed memory cell (`pointsToBytes_focus` / `stackFrameAt_split_close`), check `*Fns`/`*Code` `HasCode` hypotheses, or apply a custom step lemma before `wp_steps`
-/
#guard_msgs (info, drop error, whitespace := lax) in
set_option proofLib.wpVerbose true in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : stuckSvcCode.holds prog) :
    prog.subroutineOk "stuck_svc" stuckSvcSpec := by
  wp_init _u s0
  wp_steps

/--
info: wp_steps: stopped at pc if (v == 0#64) = true then 67084#64 else 67076#64 (target s0.readReg64 Reg.lr): branch condition unresolved at pc (condition: (v == 0#64) = true); next: use `wp_if hcond` (or prove `have hcond : ... := by bv_arith` before `wp_steps`)
-/
#guard_msgs (info, drop error, whitespace := lax) in
set_option proofLib.wpVerbose true in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : BranchFnCodeAt prog) :
    prog.subroutineOk "branch_fn" branchFnUnresolvedSpec := by
  wp_init v s0
  wp_steps

/--
info: wp_steps: stopped at pc 65536#64 (target s0.readReg64 Reg.lr): stopped at subroutine call boundary (`bl` at 65560#64); next: use `wpp_call <callee_spec>` or `wp_call <callee_spec>` (or `wp_step` to inline)
-/
#guard_msgs (info, drop error, whitespace := lax) in
set_option proofLib.wpVerbose true in
set_option maxHeartbeats 30000 in
example (prog : Program) (h_code : BumpPairCodeAt prog) :
    prog.subroutineOk "bump_pair" bumpPairSpec := by
  wp_init a s0
  wp_steps

end DiagnosticErrorTests

/-! ## `SepWPp.of_sepWP_at` and `SepWPp.panic_allowPanic_at` -/

section PanicAtTests

/-- `SepWPp.panic_allowPanic_at` closes an `⌜φ⌝ ∗ anyHeap ∗ R` panic obligation at a named
    panicking extern, with the `pc`/`status` side conditions passed explicitly. -/
example (prog : Program) (ret target : BitVec 64) (s : State) (P R : SepProp)
    (Q : State → SepProp → Prop) (oom : State → SepProp)
    (hext : prog.externAt? target = some Rust.panicked)
    (hrun : s.status = .Running) (hpc : s.pc = target) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜True⌝ ∗ anyHeap ∗ R)) oom :=
  SepWPp.panic_allowPanic_at hext trivial hrun hpc

/-- `SepWPp.of_sepWP_at` hands `sm.pc = mid` and `sm.status = .Running` to the continuation, so
    `SepWPp.panic_allowPanic_at` can close the panic path at `mid` without restating them. -/
example (prog : Program) (ret mid : BitVec 64) (s : State) (P R : SepProp)
    (Q : State → SepProp → Prop) (oom : State → SepProp)
    (hext : prog.externAt? mid = some Rust.panicked)
    (hrun : s.status = .Running) (hpc : s.pc = mid) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜True⌝ ∗ anyHeap ∗ R)) oom := by
  apply SepWPp.of_sepWP_at (mid := mid)
  refine SepWP.done hpc hrun fun hpc' hrun' => ?_
  exact SepWPp.panic_allowPanic_at hext trivial hrun' hpc'

end PanicAtTests

/-! ## `SepWP.bupd_pre` -/

section BupdPreTests

/-- `SepWP.bupd_pre` freezes a writable cell to read-only before continuing. -/
example (prog : Program) (target : BitVec 64) (s : State) (a v : BitVec 64)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWP prog target s (a ↦₆₄ᵣ v) post oom) :
    SepWP prog target s (a ↦₆₄ v) post oom :=
  SepWP.bupd_pre (pointsTo64_freeze_ro a v) h

end BupdPreTests

/-! ## Deep Preconditions in `wp_init` and `wpp_init` (`pp.deepTerms = false`) -/

section DeepPreInitTests

def deepExtra52 (q v : BitVec 64) : SepProp :=
  ((q + 0x008#64) ↦₆₄ v) ∗ ((q + 0x010#64) ↦₆₄ v) ∗ ((q + 0x018#64) ↦₆₄ v) ∗ ((q + 0x020#64) ↦₆₄ v) ∗
  ((q + 0x028#64) ↦₆₄ v) ∗ ((q + 0x030#64) ↦₆₄ v) ∗ ((q + 0x038#64) ↦₆₄ v) ∗ ((q + 0x040#64) ↦₆₄ v) ∗
  ((q + 0x048#64) ↦₆₄ v) ∗ ((q + 0x050#64) ↦₆₄ v) ∗ ((q + 0x058#64) ↦₆₄ v) ∗ ((q + 0x060#64) ↦₆₄ v) ∗
  ((q + 0x068#64) ↦₆₄ v) ∗ ((q + 0x070#64) ↦₆₄ v) ∗ ((q + 0x078#64) ↦₆₄ v) ∗ ((q + 0x080#64) ↦₆₄ v) ∗
  ((q + 0x088#64) ↦₆₄ v) ∗ ((q + 0x090#64) ↦₆₄ v) ∗ ((q + 0x098#64) ↦₆₄ v) ∗ ((q + 0x0a0#64) ↦₆₄ v) ∗
  ((q + 0x0a8#64) ↦₆₄ v) ∗ ((q + 0x0b0#64) ↦₆₄ v) ∗ ((q + 0x0b8#64) ↦₆₄ v) ∗ ((q + 0x0c0#64) ↦₆₄ v) ∗
  ((q + 0x0c8#64) ↦₆₄ v) ∗ ((q + 0x0d0#64) ↦₆₄ v) ∗ ((q + 0x0d8#64) ↦₆₄ v) ∗ ((q + 0x0e0#64) ↦₆₄ v) ∗
  ((q + 0x0e8#64) ↦₆₄ v) ∗ ((q + 0x0f0#64) ↦₆₄ v) ∗ ((q + 0x0f8#64) ↦₆₄ v) ∗ ((q + 0x100#64) ↦₆₄ v) ∗
  ((q + 0x108#64) ↦₆₄ v) ∗ ((q + 0x110#64) ↦₆₄ v) ∗ ((q + 0x118#64) ↦₆₄ v) ∗ ((q + 0x120#64) ↦₆₄ v) ∗
  ((q + 0x128#64) ↦₆₄ v) ∗ ((q + 0x130#64) ↦₆₄ v) ∗ ((q + 0x138#64) ↦₆₄ v) ∗ ((q + 0x140#64) ↦₆₄ v) ∗
  ((q + 0x148#64) ↦₆₄ v) ∗ ((q + 0x150#64) ↦₆₄ v) ∗ ((q + 0x158#64) ↦₆₄ v) ∗ ((q + 0x160#64) ↦₆₄ v) ∗
  ((q + 0x168#64) ↦₆₄ v) ∗ ((q + 0x170#64) ↦₆₄ v) ∗ ((q + 0x178#64) ↦₆₄ v) ∗ ((q + 0x180#64) ↦₆₄ v) ∗
  ((q + 0x188#64) ↦₆₄ v) ∗ ((q + 0x190#64) ↦₆₄ v) ∗ ((q + 0x198#64) ↦₆₄ v) ∗ ((q + 0x1a0#64) ↦₆₄ v)

set_option pp.deepTerms false in
theorem bump_cell_deep_wp_init_ok (prog : Program) (h_code : BumpCellCodeAt prog) :
    prog.subroutineOk "bump_cell"
      { pre  := fun (p, q, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v) ∗ deepExtra52 q v
        post := fun (p, q, v) _ _sf => (p ↦₆₄ (v + 1#64)) ∗ deepExtra52 q v } := by
  simp only [deepExtra52]
  wp_init a s0
  wp_steps
  wp_done

set_option pp.deepTerms false in
theorem bump_cell_deep_wpp_init_ok (prog : Program) (h_code : BumpCellCodeAt prog) :
    prog.subroutineOk "bump_cell"
      (Spec.allowPanicWhen
        { pre  := fun (p, q, v) s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v) ∗ deepExtra52 q v
          post := fun (p, q, v) _ _sf => (p ↦₆₄ (v + 1#64)) ∗ deepExtra52 q v }
        (fun (_, _, v) _ _ => v = 0#64)) := by
  simp only [Spec.allowPanicWhen, deepExtra52]
  wpp_init a s0
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

end DeepPreInitTests

end ProofLib.SepLogic.Tests
