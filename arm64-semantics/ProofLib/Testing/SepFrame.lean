/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# `sep_frame` Frame-Inference Regression Tests

Unit and regression tests for `ProofLib/SepLogic/FrameInfer.lean` (`sep_frame`, `sep_frame?`,
`sep_frame_apply`) and `ProofLib/SepLogic/WP/FrameAuto.lean` (`SepWP.frame_auto`,
`SepWP.call_subroutine_frame_auto`), covering frame inference, ghost backtracking, address
normalization and region carving/merging, contract projections, transparent abbreviations vs.
`@[sep_unfold]` and opaque definitions, and negative/diagnostic `#guard_msgs` cases.
-/

@[expose] public section

namespace Testing.SepFrame

open Arm64 ProofLib

variable (m : Memory) (a b c : BitVec 64) (x y z w : BitVec 64) (R : SepProp)

/-- Expose a frame metavariable to the solver: `frame_exists_of (by sep_frame?)` elaborates the
    tactic block against `m ⊨ Q ∗ ?F`. -/
theorem frame_exists_of {m : Memory} {Q F : SepProp} (h : m ⊨ Q ∗ F) : ∃ F', m ⊨ Q ∗ F' :=
  ⟨F, h⟩

/-- Two ghost cells chained through their value. -/
theorem ghost2_of {m : Memory} {p v w : BitVec 64} {F : SepProp}
    (h : m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F) : ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F :=
  ⟨p, v, F, h⟩

/-- Equation with a frame metavariable. -/
theorem eq_exists_of {P Q F : SepProp} (h : P = Q ∗ F) : ∃ F', P = Q ∗ F' := ⟨F, h⟩

/-! ## Frame inference -/

/-- info: sep_frame: frame := a ↦₆₄ x ∗ c ↦₆₄ z -/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ (c ↦₆₄ z)) : ∃ F, m ⊨ (b ↦₆₄ y) ∗ F :=
  frame_exists_of (by sep_frame?)

/-- The `hpre` premise shape of `SepWP.call_subroutine_frame` (the frame is explicit here). -/
example : ∀ R, m ⊨ ((a ↦₆₄ x) ∗ (b ↦₆₄ y)) ∗ R → m ⊨ (b ↦₆₄ y) ∗ ((a ↦₆₄ x) ∗ R) := by
  sep_frame

example : (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ R ⊢ R ∗ (a ↦₆₄ x) ∗ (b ↦₆₄ y) := by
  sep_frame

/-- info: sep_frame: frame := a ↦₆₄ x ∗ R -/
#guard_msgs in
example : ∃ F, ((a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ R) = (b ↦₆₄ y) ∗ F :=
  eq_exists_of (by sep_frame?)

example (F : SepProp) (h : SepFrame (b ↦₆₄ y) ((a ↦₆₄ x) ∗ (b ↦₆₄ y)) F) :
    SepFrame (b ↦₆₄ y) ((b ↦₆₄ y) ∗ (a ↦₆₄ x)) F := by
  have := h.eq
  exact ⟨by rw [sepConj_comm]; exact this⟩

example : ∃ F, SepFrame (b ↦₆₄ y) ((a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ R) F :=
  ⟨_, by sep_frame⟩

/-! ## Ghost metavariables with backtracking -/

/-- The first candidate for `?p ↦₆₄ ?v` (`a ↦₆₄ x`) leaves `x ↦₆₄ w` unmatched; the solver
    backtracks to `b ↦₆₄ y`. The greedy `sep_entail` matcher fails on the same goal. -/
example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ (y ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F :=
  ghost2_of (by
    (fail_if_success sep_entail)
    sep_frame)

/-- info: sep_frame: frame := a ↦₆₄ x -/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ (y ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F :=
  ghost2_of (by sep_frame?)

/-! ## Normalization, regions, pure and existential atoms, side conditions -/

example (s : State) (sp : BitVec 64) (hsp : s.sp = sp)
    (h : m ⊨ ((sp + 8#64) ↦₆₄ x) ∗ stackAt sp 32) :
    m ⊨ stackAt s.sp 32 ∗ ((s.sp + 4#64 + 4#64) ↦₆₄ x) := by
  sep_frame

-- Carving a callee stack frame out of a larger caller region.
/-- info: sep_frame: frame := R ∗ memRegion (sp - 64#64) 48 -/
#guard_msgs in
example (sp : BitVec 64) (h : m ⊨ stackAt sp 64 ∗ R) : ∃ F, m ⊨ stackAt sp 16 ∗ F :=
  frame_exists_of (by sep_frame?)

/-- info: sep_frame: frame := memRegion a 16 ∗ memRegion (a + 24#64) 40 -/
#guard_msgs in
example (h : m ⊨ memRegion a 64) : ∃ F, m ⊨ memRegion (a + 16#64) 8 ∗ F :=
  frame_exists_of (by sep_frame?)

-- Merging the pieces back.
example (sp : BitVec 64) (h : m ⊨ memRegion (sp - 64#64) 48 ∗ stackAt sp 16) :
    m ⊨ stackAt sp 64 := by
  sep_frame

example (hx : x = 7#64) (h : m ⊨ (a ↦₆₄ x) ∗ R) :
    m ⊨ ⌜x = 7#64⌝ ∗ (∃∗ v, a ↦₆₄ v) ∗ R := by
  sep_frame

example (hxy : x = y) (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ R ∗ (a ↦₆₄ y) := by
  sep_frame

example (hxy : y = x) (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ R ∗ (a ↦₆₄ y) := by
  sep_frame (disch := exact hxy.symm)

/-! ## Contract projections and ghost tuples -/

structure Widget where
  pre : BitVec 64 → BitVec 64 → SepProp

def widgetSpec (a : BitVec 64) : Widget where
  pre := fun v r => (a ↦₆₄ v) ∗ (r ↦₆₄ a)

theorem widget_of {m : Memory} {a v r : BitVec 64} {F : SepProp}
    (h : m ⊨ (widgetSpec a).pre v r ∗ F) : ∃ v r F, m ⊨ (widgetSpec a).pre v r ∗ F :=
  ⟨v, r, F, h⟩

/-- info: sep_frame: frame := R -/
#guard_msgs in
example (h : m ⊨ (b ↦₆₄ a) ∗ (a ↦₆₄ x) ∗ R) : ∃ v r F, m ⊨ (widgetSpec a).pre v r ∗ F :=
  widget_of (by sep_frame?)

structure Codec where
  pre : BitVec 64 × BitVec 64 → SepProp

def codecSpec : Codec where
  pre := fun (p, v) => (p ↦₆₄ v)

theorem codec_of {m : Memory} {x : BitVec 64 × BitVec 64} {F : SepProp}
    (h : m ⊨ codecSpec.pre x ∗ F) : ∃ x F, m ⊨ codecSpec.pre x ∗ F := ⟨x, F, h⟩

/-- info: sep_frame: frame := R -/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ R) : ∃ x F, m ⊨ codecSpec.pre x ∗ F :=
  codec_of (by sep_frame?)

/-! ## `SepWP` rules and tactics -/

example (prog : Program) (pc : BitVec 64) (s : State) (Q : State → Prop) (P' : SepProp)
    (h : SepWP prog pc s (a ↦₆₄ x) (fun sf Pf => (Pf ⊢ P') ∧ Q sf)) :
    SepWP prog pc s ((b ↦₆₄ y) ∗ (a ↦₆₄ x) ∗ R)
      (fun sf Pf => (Pf ⊢ P' ∗ ((b ↦₆₄ y) ∗ R)) ∧ Q sf) :=
  SepWP.frame_auto h

example (prog : Program) (pc : BitVec 64) (s : State) (Q : State → Prop) (P' : SepProp)
    (h : SepWP prog pc s (a ↦₆₄ x) (fun sf Pf => (Pf ⊢ P') ∧ Q sf)) :
    SepWP prog pc s ((b ↦₆₄ y) ∗ (a ↦₆₄ x) ∗ R)
      (fun sf Pf => (Pf ⊢ P' ∗ ((b ↦₆₄ y) ∗ R)) ∧ Q sf) := by
  sep_frame_apply SepWP.frame_post_entails h

/-- `sep_frame_apply` inside `SepWP.seq`: the intermediate context is computed, not written. -/
example (prog : Program) (pc pc2 : BitVec 64) (s : State) (Q : State → Prop) (P' : SepProp)
    (post : State → SepProp → Prop)
    (h : SepWP prog pc s (a ↦₆₄ x) (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = pc → s1.status = .Running → Q s1 → ∀ F, SepWP prog pc2 s1 (P' ∗ F) post) :
    SepWP prog pc2 s ((b ↦₆₄ y) ∗ (a ↦₆₄ x) ∗ R) post := by
  refine SepWP.seq (by sep_frame_apply SepWP.frame_post_entails h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

/-- A callee contract with a pure register fact, an owned cell and a 32-byte stack frame. -/
def bumpSpec : Spec (BitVec 64) where
  pre := fun p s => ⌜s.readReg64 .x0 = p⌝ ∗ (∃∗ v, p ↦₆₄ v) ∗ stackAt s.sp 32
  post := fun p s0 _ => (p ↦₆₄ 0#64) ∗ stackAt s0.sp 32

/-- `SepWP.call_subroutine_frame_auto`: no `(F := ...)`, no stack split, no `ac_rfl`; the frame is
    `(sp + 8 ↦₆₄ y) ∗ R ∗ memRegion (sp - 96#64) 64` (the rest of the caller stack). -/
example (prog : Program) (entry target ret : BitVec 64) (post : State → SepProp → Prop)
    (hcall : subroutine_ok prog entry bumpSpec) (s : State) (sp p : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = p)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf (bumpSpec.post p s sf ∗ F) post) :
    SepWP prog target s ((p ↦₆₄ x) ∗ ((sp + 8#64) ↦₆₄ y) ∗ R ∗ stackAt sp 96) post := by
  refine SepWP.call_subroutine_frame_auto hcall hpc hrun halign hlr ?_ ?_ ?_
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

/-- The `wp_frame_split` fallback: the greedy matcher fails on chained ghosts, the backtracking
    frame procedure succeeds. -/
example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ (y ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F :=
  ghost2_of (by wp_frame_split)

/-! ## Transparent abbreviations and local definitions -/

/-- A transparent two-cell predicate: `sep_frame` unfolds `abbrev` atoms whose body is a `∗`-tree. -/
abbrev twoCells (p q v w : BitVec 64) : SepProp := (p ↦₆₄ v) ∗ (q ↦₆₄ w)

/-- The same body as a `def`: stays a single opaque atom. -/
def twoCellsOpaque (p q v w : BitVec 64) : SepProp := (p ↦₆₄ v) ∗ (q ↦₆₄ w)

/-- info: sep_frame: frame := a ↦₆₄ x -/
#guard_msgs in
example (h : m ⊨ twoCells a b x y ∗ (c ↦₆₄ z)) : ∃ F, m ⊨ ((c ↦₆₄ z) ∗ (b ↦₆₄ y)) ∗ F :=
  frame_exists_of (by sep_frame?)

/-- Let-bound locals (`let F := ...` / `set F := ...`) are unfolded too. -/
example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ (c ↦₆₄ z)) :
    let F : SepProp := (a ↦₆₄ x) ∗ (b ↦₆₄ y)
    m ⊨ (c ↦₆₄ z) ∗ F := by
  sep_frame

/-- Let-bound values inside atoms (`set p := a + 8#64` used as an address) are unfolded. -/
example (h : m ⊨ ((a + 8#64) ↦₆₄ x) ∗ R) :
    let p := a + 8#64
    m ⊨ R ∗ (p ↦₆₄ x) := by
  sep_frame

/-- Addresses `x + (y + c)` and `x + y + c` (literal `c`) are identified. -/
example (h : m ⊨ ((a + (b + 8#64)) ↦₆₄ x) ∗ R) : m ⊨ R ∗ ((a + b + 8#64) ↦₆₄ x) := by
  sep_frame

/-- A `def` atom matches itself. -/
example (h : m ⊨ (c ↦₆₄ z) ∗ twoCellsOpaque a b x y) : m ⊨ twoCellsOpaque a b x y ∗ (c ↦₆₄ z) := by
  sep_frame

/-- A user-defined single-atom region abbreviation (not `ProofLib.stackAt`). -/
abbrev localStackBelow (sp : BitVec 64) (n : Nat) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 n) n

/-- A user-defined stack budget constant and nested region abbreviation. -/
abbrev localHookBytes : Nat := 4096
abbrev localHookFrame (sp : BitVec 64) : SepProp :=
  localStackBelow sp localHookBytes

-- Merging adjacent `localStackBelow` slices into `localStackBelow _ localHookBytes` and
-- `localHookFrame` without `dsimp`, keeping unmatched `localStackBelow` atoms folded in
-- the inferred frame.
/-- info: sep_frame: frame := localStackBelow (sp - 4096#64) 48 -/
#guard_msgs in
example (sp : BitVec 64)
    (h : m ⊨ localStackBelow (sp - 80#64) 4064 ∗ localStackBelow (sp - 48#64) 32 ∗
      localStackBelow (sp - 4096#64) 48) :
    ∃ F, m ⊨ localStackBelow (sp - 48#64) localHookBytes ∗ F :=
  frame_exists_of (by sep_frame?)

example (sp : BitVec 64)
    (h : m ⊨ localStackBelow (sp - 80#64) 4064 ∗ localStackBelow (sp - 48#64) 32) :
    m ⊨ localHookFrame (sp - 48#64) := by
  sep_frame

-- Carving a callee `localHookFrame` out of a caller `localStackBelow`.
/-- info: sep_frame: frame := memRegion (sp - 32#64) 32 -/
#guard_msgs in
example (sp : BitVec 64) (h : m ⊨ localStackBelow sp (32 + localHookBytes)) :
    ∃ F, m ⊨ localHookFrame (sp - 32#64) ∗ F :=
  frame_exists_of (by sep_frame?)

/-- A single-cell `abbrev` wrapper is unfolded in `atomKey` and normalized. -/
abbrev localField (p v : BitVec 64) : SepProp := (p + 8#64) ↦₆₄ v

example (h : m ⊨ ((a + 4#64 + 4#64) ↦₆₄ x) ∗ R) : m ⊨ R ∗ localField a x := by
  sep_frame

/-! ## Negative tests -/

/--
error: sep_frame: no hypothesis atom matches goal atom
  a ↦₆₄ x
unmatched hypothesis atoms: twoCellsOpaque a b x y
hint: context atom `twoCellsOpaque a b x
  y` uses composite definition `Testing.SepFrame.twoCellsOpaque` while target atom `a ↦₆₄
  x` is a raw spatial atom; unfold or fold `Testing.SepFrame.twoCellsOpaque` so both sides are at the same abstraction level
-/
#guard_msgs in
example (h : m ⊨ twoCellsOpaque a b x y) : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) := by
  sep_frame

/--
error: sep_frame: no hypothesis atom matches goal atom
  b ↦₆₄ y
unmatched hypothesis atoms: a ↦₆₄ x
-/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ (b ↦₆₄ y) ∗ R := by
  sep_frame

/--
error: sep_frame: unmatched hypothesis atoms in an entailment/equation goal without a frame metavariable: a ↦₆₄ x
-/
#guard_msgs in
example : (a ↦₆₄ x) ∗ R ⊢ R := by
  sep_frame

/--
error: sep_frame: cannot prove the value side condition
  x = y
-/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ R ∗ (a ↦₆₄ y) := by
  sep_frame

/--
error: sep_frame: search budget exhausted after 1 candidate pairings (raise `proofLib.sepFrameMaxSteps`, or give some frame/ghost arguments explicitly)
-/
#guard_msgs in
set_option proofLib.sepFrameMaxSteps 1 in
example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ (y ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F :=
  ghost2_of (by sep_frame)

/--
error: sep_frame: no hypothesis atom matches goal atom
  stackAt sp 128
(normalized:
  memRegion (sp - 128#64) 128)
unmatched hypothesis atoms: stackAt sp 64
-/
#guard_msgs in
example (sp : BitVec 64) (h : m ⊨ stackAt sp 64) : m ⊨ stackAt sp 128 := by
  sep_frame

/--
error: sep_frame: no hypothesis atom matches goal atom
  localStackBelow sp 128
(normalized:
  memRegion (sp - 128#64) 128)
unmatched hypothesis atoms: localStackBelow sp 64
-/
#guard_msgs in
example (sp : BitVec 64) (h : m ⊨ localStackBelow sp 64) : m ⊨ localStackBelow sp 128 := by
  sep_frame

/-! ## `frame_split`, `sep_focus`, `sep_entail`, and `sep_frame` diagnostic hints -/

-- `frame_split` same-address value near-miss (after address normalization).
/--
error: frame_split: no match for (a + 8#64) ↦₆₄ y in precondition
  near-miss at same address: target expects `(a + 8#64) ↦₆₄
  y`, but context has `(a + 8#64) ↦₆₄
  x` (prove the values equal with `rw`/`simp` before matching, or split/coalesce cell widths)
candidates: (a + 8#64) ↦₆₄ x
-/
#guard_msgs in
example (h : m ⊨ ((a + 8#64) ↦₆₄ x) ∗ R) : m ⊨ ((a + 4#64 + 4#64) ↦₆₄ y) ∗ R := by
  wp_frame_split

-- `frame_split` same-address width near-miss.
/--
error: frame_split: no match for a ↦₃₂ BitVec.truncate 32 x in precondition
  near-miss at same address: target expects `a ↦₃₂
  BitVec.truncate 32
    x`, but context has `a ↦₆₄
  x` (prove the values equal with `rw`/`simp` before matching, or split/coalesce cell widths)
candidates: a ↦₆₄ x
-/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ (a ↦₃₂ (x.truncate 32)) ∗ R := by
  wp_frame_split

-- `frame_split` region/slice container at the same base.
/--
error: frame_split: no match for (a + 8#64) ↦₆₄ x in precondition
hint: context contains region/slice atom `a ↦ₛ
  bs` at the same base; carve or split the window with `pointsToBytes_focus` / `memRegion_split_le` / `stackFrameAt_split_close`
candidates: a ↦ₛ bs
-/
#guard_msgs in
example (bs : List (BitVec 8)) (h : m ⊨ (a ↦ₛ bs) ∗ R) : m ⊨ ((a + 8#64) ↦₆₄ x) ∗ R := by
  wp_frame_split

-- `frame_split` target composite predicate vs. raw context cells.
/--
error: frame_split: no match for twoCellsOpaque a b x y in precondition
hint: target atom `twoCellsOpaque a b x
  y` uses composite definition `Testing.SepFrame.twoCellsOpaque`; unfold or fold `Testing.SepFrame.twoCellsOpaque` so both sides are at the same abstraction level
candidates: a ↦₆₄ x, b ↦₆₄ y
-/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y)) : m ⊨ twoCellsOpaque a b x y ∗ emp := by
  wp_frame_split

-- `frame_split` context composite predicate vs. raw target cell.
/--
error: frame_split: no match for a ↦₆₄ x in precondition
hint: context atom `twoCellsOpaque a b x
  y` uses composite definition `Testing.SepFrame.twoCellsOpaque` while target atom `a ↦₆₄
  x` is a raw spatial atom; unfold or fold `Testing.SepFrame.twoCellsOpaque` so both sides are at the same abstraction level
candidates: twoCellsOpaque a b x y
-/
#guard_msgs in
example (h : m ⊨ twoCellsOpaque a b x y) : m ⊨ (a ↦₆₄ x) ∗ emp := by
  wp_frame_split

-- `sep_focus` goal-shape routing hints (`Entails`, `Satisfies`, `SepWP`).
set_option proofLib.sepShapeDispatch false in
/--
error: sep_focus: goal is not an equation (goal head: `Arm64.SepProp.Entails`)
  actual goal: a ↦₆₄ x ∗ R ⊢ a ↦₆₄ x ∗ R
hint: use `sep_entail` or `sep_frame` to discharge entailment/satisfaction goals
-/
#guard_msgs in
example : (a ↦₆₄ x) ∗ R ⊢ (a ↦₆₄ x) ∗ R := by
  sep_focus

set_option proofLib.sepShapeDispatch false in
/--
error: sep_focus: goal is not an equation (goal head: `Arm64.SepProp.Satisfies`)
  actual goal: m ⊨ a ↦₆₄ x ∗ R
hint: use `sep_entail` or `sep_frame` to discharge entailment/satisfaction goals
-/
#guard_msgs in
example (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ (a ↦₆₄ x) ∗ R := by
  sep_focus

/--
error: sep_focus: goal is not an equation (goal head: `ProofLib.SepWP`)
  actual goal: SepWP prog (0#64) s (a ↦₆₄ x ∗ R) Q
hint: `sep_focus` operates on `P = Q ∗ R` equations; to rewrite the `SepWP` precondition, use `wp_conv_pre => ...` or `rw [pointsToBytes_focus ...]`
-/
#guard_msgs in
example (prog : Program) (s : State) (Q : State → SepProp → Prop) :
    SepWP prog 0#64 s ((a ↦₆₄ x) ∗ R) Q := by
  sep_focus

-- `sep_entail` (`sep solver`) goal-shape routing hints (`∀ m, m ⊨ P → m ⊨ Q`, `SepWP`).
set_option proofLib.sepShapeDispatch false in
/--
error: sep solver: goal is not of the form `m ⊨ P` (goal head: `∀`)
  actual goal: ∀ (m : Memory), m ⊨ a ↦₆₄ x → m ⊨ a ↦₆₄ x
hint: run `intro m hm; sep_entail`
-/
#guard_msgs in
example : ∀ m : Memory, m ⊨ (a ↦₆₄ x) → m ⊨ (a ↦₆₄ x) := by
  sep_entail

/--
error: sep solver: goal is not of the form `m ⊨ P` (goal head: `ProofLib.SepWP`)
  actual goal: SepWP prog (0#64) s (a ↦₆₄ x) Q
hint: goal is a `SepWP` weakest precondition; use `wp_done` (at target PC) or `wp_steps`
-/
#guard_msgs in
example (prog : Program) (s : State) (Q : State → SepProp → Prop) :
    SepWP prog 0#64 s (a ↦₆₄ x) Q := by
  sep_entail

-- `sep_frame` goal-shape routing hint (`SepWP`).
/--
error: sep_frame: expected a goal `m ⊨ Q`, `∀ R, m ⊨ P ∗ R → m ⊨ Q`, `P ⊢ Q`, `P = Q` or `SepFrame Sub Full F` (goal head: `ProofLib.SepWP`), got
  SepWP prog (0#64) s (a ↦₆₄ x) Q
hint: goal is a `SepWP` weakest precondition; use `wp_done` (at target PC), `wp_steps`, or `wp_conv_pre => ...` to rewrite the precondition
-/
#guard_msgs in
example (prog : Program) (s : State) (Q : State → SepProp → Prop) :
    SepWP prog 0#64 s (a ↦₆₄ x) Q := by
  sep_frame

/-! ## Automatic tactic behaviors -/

-- Near-miss value equality in `wp_frame_split`, `sep_focus`, and `sep_entail`.
example (hxy : x = y) (h : m ⊨ ((a + 8#64) ↦₆₄ x) ∗ R) :
    m ⊨ ((a + 4#64 + 4#64) ↦₆₄ y) ∗ R := by
  wp_frame_split

example (hxy : x = y) :
    ∃ F, (((a + 8#64) ↦₆₄ x) ∗ R = ((a + 4#64 + 4#64) ↦₆₄ y) ∗ F) :=
  eq_exists_of (by sep_focus)

example (hxy : x = y) :
    ((a + 8#64) ↦₆₄ x) ∗ R ⊢ ((a + 4#64 + 4#64) ↦₆₄ y) ∗ R := by
  sep_entail

-- With `proofLib.frameSplitLeaveSideGoals`, leave value equality open as a subgoal.
set_option proofLib.frameSplitLeaveSideGoals true in
example (g : ∀ k : Nat, k + k = 2 → x = y) (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ (a ↦₆₄ y) ∗ R := by
  sep_entail
  exact g 1 rfl

set_option proofLib.frameSplitLeaveSideGoals true in
example (g : ∀ k : Nat, k + k = 2 → x = y) (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ (a ↦₆₄ y) ∗ R := by
  sep_frame
  exact g 1 rfl

-- Automatic container splitting (`stackFrameAt` and `pointsToBytes`).
example (sp : BitVec 64) :
    ∃ F, stackFrameAt sp 32 = (∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v) ∗ F :=
  eq_exists_of (by sep_focus)

example (sp : BitVec 64) (h : m ⊨ stackFrameAt sp 32 ∗ R) :
    m ⊨ (∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v) ∗ memRegion (sp - 32#64) 16 ∗ memRegion (sp - 8#64) 8 ∗ R := by
  sep_entail

example (sp : BitVec 64) (h : m ⊨ stackFrameAt sp 32 ∗ R) :
    ∃ F, m ⊨ (∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v) ∗ F :=
  frame_exists_of (by sep_frame)

example (bs : List (BitVec 8)) (hlen : bs.length = 16) :
    ∃ F, (a ↦ₛ bs) ∗ R = ((a + 8#64) ↦₈ bs.getD 8 0#8) ∗ F :=
  eq_exists_of (by sep_focus)

example (bs : List (BitVec 8)) (hlen : bs.length = 16) (h : m ⊨ (a ↦ₛ bs) ∗ R) :
    ∃ F, m ⊨ ((a + 8#64) ↦₈ bs.getD 8 0#8) ∗ F :=
  frame_exists_of (by sep_frame)

-- `@[sep_unfold]` composite predicate unfolding in both directions.
@[sep_unfold]
def taggedPair (a b x y : BitVec 64) : SepProp := (a ↦₆₄ x) ∗ (b ↦₆₄ y)

example (h : m ⊨ (a ↦₆₄ x) ∗ (b ↦₆₄ y) ∗ R) : m ⊨ taggedPair a b x y ∗ R := by
  wp_frame_split

example (h : m ⊨ taggedPair a b x y ∗ R) :
    ∃ F, m ⊨ (a ↦₆₄ x) ∗ F :=
  frame_exists_of (by sep_frame)

example : ∃ F, taggedPair a b x y ∗ R = (a ↦₆₄ x) ∗ F :=
  eq_exists_of (by sep_focus)

example (h : m ⊨ taggedPair a b x y ∗ R) : m ⊨ taggedPair a b x y ∗ R := by
  sep_frame

-- Goal-shape dispatch in `sep_focus` and `sep_entail`.
example : (a ↦₆₄ x) ∗ R ⊢ R ∗ (a ↦₆₄ x) := by
  sep_focus

example (h : m ⊨ (a ↦₆₄ x) ∗ R) : m ⊨ R ∗ (a ↦₆₄ x) := by
  sep_focus

example : (a ↦₆₄ x) ∗ R = R ∗ (a ↦₆₄ x) := by
  sep_focus

example : ∀ m : Memory, m ⊨ (a ↦₆₄ x) ∗ R → m ⊨ R ∗ (a ↦₆₄ x) := by
  sep_entail

/-! ## Spatial near-miss auto-closing and `bv_arith` diagnostics -/

-- Slice address + `toNat` length near-miss closed automatically across `wp_frame_split`,
-- `sep_entail`, `sep_focus`, and `SepFrame` (`let`-bound `b_pow` + hypothesis `h_ctrl`).
example (ptr new_ctrl : BitVec 64) (k' : Nat)
    (h_ctrl : new_ctrl = ptr + BitVec.ofNat 64 (2 ^ k') <<< 4)
    (h : m ⊨ ((ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ
      List.replicate (BitVec.ofNat 64 (2 ^ k' + 8)).toNat 255#8) ∗ R) :
    let b_pow := BitVec.ofNat 64 (2 ^ k')
    m ⊨ (new_ctrl ↦ₛ List.replicate (b_pow + 8#64).toNat 255#8) ∗ R := by
  intro b_pow
  wp_frame_split

example (ptr new_ctrl : BitVec 64) (k' : Nat)
    (h_ctrl : new_ctrl = ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) :
    let b_pow := BitVec.ofNat 64 (2 ^ k')
    ∃ F, ((ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ
      List.replicate (BitVec.ofNat 64 (2 ^ k' + 8)).toNat 255#8) ∗ R =
      (new_ctrl ↦ₛ List.replicate (b_pow + 8#64).toNat 255#8) ∗ F := by
  intro b_pow
  exact eq_exists_of (by sep_focus)

example (ptr new_ctrl : BitVec 64) (k' : Nat)
    (h_ctrl : new_ctrl = ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) :
    let b_pow := BitVec.ofNat 64 (2 ^ k')
    SepFrame
      (new_ctrl ↦ₛ List.replicate (b_pow + 8#64).toNat 255#8)
      (((ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ
        List.replicate (BitVec.ofNat 64 (2 ^ k' + 8)).toNat 255#8) ∗ R)
      R := by
  intro b_pow
  wp_frame_split

example (ptr new_ctrl : BitVec 64) (k' : Nat)
    (hk : 2 ^ k' + 8 < 2 ^ 64)
    (h_ctrl : new_ctrl - ptr = BitVec.ofNat 64 (2 ^ k') <<< 4)
    (h : m ⊨ ((ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ
      List.replicate (2 ^ k' + 8) 255#8) ∗ R) :
    let b_pow := BitVec.ofNat 64 (2 ^ k')
    m ⊨ (new_ctrl ↦ₛ List.replicate (b_pow + 8#64).toNat 255#8) ∗ R := by
  intro b_pow
  wp_frame_split

-- `arm64_norm` / `bv_lin` address normalization + hypothesis rewriting + value extraction.
example (sp dst v : BitVec 64)
    (hdst : dst = (sp - 48#64) + (8#64 + 8#64))
    (h : m ⊨ ((if false = true then sp else (sp - 48#64) + 16#64) ↦₆₄ v) ∗ R) :
    m.read64 dst = v :=
  read64_sep_at dst h

-- `omega` after `toNat` length equality + address hypothesis on `memRegion`.
example (ptr dst bv : BitVec 64)
    (hdst : dst = ptr + 16#64)
    (hb : bv.toNat + 8 < 2 ^ 64)
    (h : m ⊨ memRegion (ptr + (8#64 + 8#64)) (bv + 8#64).toNat ∗ R) :
    m ⊨ memRegion dst (bv.toNat + 8) ∗ R := by
  wp_frame_split

-- Negative `#guard_msgs`: unproved address near-miss reports remaining equality + `bv_arith` snippet.
/--
error: frame_split: no match for new_ctrl ↦ₛ List.replicate len 255#8 in precondition
  near-miss: target expects `new_ctrl ↦ₛ
  List.replicate len
    255#8`, context has `(ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ
  List.replicate len 255#8`; remaining equality: `new_ctrl = ptr + BitVec.ofNat 64 (2 ^ k') <<< 4`
  hint: `have h : new_ctrl = ptr + BitVec.ofNat 64 (2 ^ k') <<< 4 := by bv_arith`
candidates: (ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ List.replicate len 255#8
-/
#guard_msgs in
example (ptr new_ctrl : BitVec 64) (k' len : Nat)
    (h : m ⊨ ((ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ List.replicate len 255#8) ∗ R) :
    m ⊨ (new_ctrl ↦ₛ List.replicate len 255#8) ∗ R := by
  wp_frame_split

-- Pasting the `have h : ... := by bv_arith` snippet emitted above closes `wp_frame_split`.
example (ptr new_ctrl : BitVec 64) (k' len : Nat)
    (h_step : new_ctrl - ptr = BitVec.ofNat 64 (2 ^ k') <<< 4)
    (h : m ⊨ ((ptr + BitVec.ofNat 64 (2 ^ k') <<< 4) ↦ₛ List.replicate len 255#8) ∗ R) :
    m ⊨ (new_ctrl ↦ₛ List.replicate len 255#8) ∗ R := by
  have h : new_ctrl = ptr + BitVec.ofNat 64 (2 ^ k') <<< 4 := by bv_arith
  wp_frame_split

-- Negative `#guard_msgs`: when the address near-miss unifies via `let`, only the length equality remains.
/--
error: frame_split: no match for new_ctrl ↦ₛ List.replicate bad_len 255#8 in precondition
  near-miss: target expects `new_ctrl ↦ₛ
  List.replicate bad_len
    255#8`, context has `(ptr + 16#64) ↦ₛ List.replicate len 255#8`; remaining equality: `bad_len = len`
  hint: `have h : bad_len = len := by bv_arith`
candidates: (ptr + 16#64) ↦ₛ List.replicate len 255#8
-/
#guard_msgs in
example (ptr : BitVec 64) (bad_len len : Nat)
    (h : m ⊨ ((ptr + 16#64) ↦ₛ List.replicate len 255#8) ∗ R) :
    let new_ctrl := ptr + 16#64
    m ⊨ (new_ctrl ↦ₛ List.replicate bad_len 255#8) ∗ R := by
  intro new_ctrl
  wp_frame_split

end Testing.SepFrame
