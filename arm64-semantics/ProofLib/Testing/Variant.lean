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
public import ProofLib.ProgramReflection.Variant

/-!
# Program Variant Transfer Tests

Regression tests for `ProofLib.ProgramReflection.Variant`: transferring non-panicking and
panicking `subroutine_ok` contracts across panic/trap hook variants via `PanicsOrTrapsOnly`,
`TrapsOnly`, `trap_transfer`, `declare_variant_kind`, `variant_map`, `#derive_variant`, and
`#guard_same_type`.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.Variant

open Arm64
open _root_.ProofLib
open _root_.ProofLib.ProgramReflection
open _root_.ProofLib.GenDecodes
open _root_.ProofLib.Variant

/-! ## Toy ARM64 Program (`checked_inc`) with Panic and Trap Stubs -/

/-- Balanced 4-word `WordTree` for `checkedIncRawProg`:
    - `0x00`: `cbz x0, 0x0c`    (`0xb4000060`) - if `x0 = 0`, branch to panic stub at `0x0c`
    - `0x04`: `add x0, x0, #1`  (`0x91000400`) - `x0 := x0 + 1`
    - `0x08`: `ret`             (`0xd65f03c0`) - return
    - `0x0c`: `udf #0`          (`0x00000000`) - panic stub placeholder at offset `0x0c` -/
def checkedIncRawProg_tree : WordTree :=
  .node 2
    (.node 1
      (.leaf 0x60#8 0x00#8 0x00#8 0xb4#8)  -- 0x00: cbz x0, 0x0c   (0xb4000060)
      (.leaf 0x00#8 0x04#8 0x00#8 0x91#8)) -- 0x04: add x0, x0, #1 (0x91000400)
    (.node 1
      (.leaf 0xc0#8 0x03#8 0x5f#8 0xd6#8)  -- 0x08: ret            (0xd65f03c0)
      (.leaf 0x00#8 0x00#8 0x00#8 0x00#8)) -- 0x0c: udf #0         (0x00000000)

/-- Rust panic symbol name (recognized by `Rust.isPanicSymbol`). -/
abbrev panicBoundsSym : String := "core::option::unwrap_failed"

/-- Relocatable `checked_inc` program with a panic stub at `0x0c` and an auxiliary stub at `0x10`. -/
def checkedIncRawProg : Program :=
  { base := 0#64
    code := checkedIncRawProg_tree.toBytes
    symbols := [("checked_inc", 0x00)]
    stubs := [
      (panicBoundsSym, 0x0c),
      ("aux_trap",     0x10)
    ] }

@[simp, arm64_norm]
theorem checkedIncRawProg_fnOff_checked_inc : checkedIncRawProg.fnOff "checked_inc" = 0 := rfl

theorem checkedIncRawProg_fetch_at (off : Nat) (inst : Instr)
    (h : checkedIncRawProg_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64) :
    checkedIncRawProg.fetch (BitVec.ofNat 64 off) = some inst := by
  simpa [checkedIncRawProg] using
    fetch_of_wordTree (prog := checkedIncRawProg) (t := checkedIncRawProg_tree) 4 rfl rfl h hoff
      (hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) off)

theorem checkedIncRawProg_fetch_rebase_text (b : BitVec 64) (X : String → Option (State → State))
    (off : Nat) (inst : Instr) (h : checkedIncRawProg_tree.fetchDecodeAt off = some inst)
    (htext : off < 12) (hoff : off < 2 ^ 64) :
    (checkedIncRawProg.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :=
  (Program.fetch_rebase_of_noStubBefore (P := checkedIncRawProg) rfl (fun _ => rfl) (fun _ => rfl)
    rfl b X htext hoff).trans (checkedIncRawProg_fetch_at off inst h hoff)

gen_fetches checkedIncRawProg checkedInc 12 true [0 → 8]

@[simp, arm64_norm] theorem checkedInc_extern_0c {b : BitVec 64}
    {H : String → Option (State → State)} :
    (checkedIncRawProg.rebase b H).externAt? (b + 12#64) = H panicBoundsSym := by
  rw [Program.externAt?_rebase_add (P := checkedIncRawProg) (b := b) (X := H)
    (O := fun _ => none) 12]
  simp (config := { decide := true }) [Program.hookAtOff?, Program.rebase, checkedIncRawProg,
    panicBoundsSym, List.findSome?, Option.or]
  cases H panicBoundsSym <;> rfl

declare_rebased_program checkedIncFixed (0x500000#64 : BitVec 64) checkedIncRawProg

@[irreducible, wp_unfold]
def checkedIncProg (b : BitVec 64) (X : String → Option (State → State) := fun _ => none) :
    Program :=
  checkedIncRawProg.rebase b X

def checkedIncPanicProg (b : BitVec 64) (X : String → Option (State → State) := fun _ => none) :
    Program :=
  checkedIncRawProg.rebase b (Rust.withPanics X)

def checkedIncTrapAndPanicProg (b : BitVec 64)
    (X : String → Option (State → State) := fun _ => none) : Program :=
  checkedIncRawProg.rebase b (trapAt (· == "aux_trap") (trapHook "aux fault") (Rust.withPanics X))

def checkedIncCustomPanicProg (b : BitVec 64) (G X : String → Option (State → State)) : Program :=
  checkedIncRawProg.rebase b (fun n => if Rust.isPanicSymbol n then G n else X n)

theorem checkedInc_trapsOnly (b : BitVec 64) (X : String → Option (State → State)) :
    TrapsOnly (checkedIncTrapAndPanicProg b X) (checkedIncPanicProg b X) := by
  unfold checkedIncTrapAndPanicProg checkedIncPanicProg
  exact TrapsOnly.rebase checkedIncRawProg b
    (HooksTrapOnly.trapAt (trapHook_isTrap _) _)

theorem checkedInc_panicsOrTrapsOnly (b : BitVec 64) (X : String → Option (State → State)) :
    PanicsOrTrapsOnly (checkedIncPanicProg b X) (checkedIncProg b X) := by
  simp only [checkedIncPanicProg, wp_unfold]
  exact PanicsOrTrapsOnly.rebase checkedIncRawProg b
    (HooksPanicOrTrapOnly.withPanics_left X)

theorem checkedInc_panicsOrTrapsOnly_fixed :
    PanicsOrTrapsOnly (checkedIncPanicProg 0x500000#64 (fun _ => none)) checkedIncFixed := by
  simp only [checkedIncPanicProg, wp_unfold]
  exact PanicsOrTrapsOnly.rebase checkedIncRawProg 0x500000#64
    (HooksPanicOrTrapOnly.withPanics_left _)

theorem checkedInc_panicsOrTrapsOnly_custom (b : BitVec 64)
    (G X : String → Option (State → State)) :
    PanicsOrTrapsOnly (checkedIncPanicProg b X) (checkedIncCustomPanicProg b G X) := by
  unfold checkedIncPanicProg checkedIncCustomPanicProg
  rw [withPanics_eq_panicAt]
  exact PanicsOrTrapsOnly.rebase checkedIncRawProg b
    (HooksPanicOrTrapOnly.panicAt_replace Rust.isPanicSymbol G X)

/-! ### Non-panicking contract transfer -/

def checkedIncNonZeroSpec : Spec (BitVec 64) :=
  { pre  := fun x s => ⌜s.readReg64 .x0 = x ∧ x ≠ 0#64⌝
    post := fun x s0 sf => ⌜sf.readReg64 .x0 = x + 1#64 ∧ sf.sp = s0.sp ∧
                            CalleeSavedPreserved s0 sf⌝ }

theorem checked_inc_panic_variant_ok (b : BitVec 64) (X : String → Option (State → State)) :
    (checkedIncPanicProg b X).subroutineOk "checked_inc" checkedIncNonZeroSpec := by
  wp_init x s0
  have hne : x ≠ 0#64 := ‹_›
  wp_step
  wp_cases
  · exact (hne hcond).elim
  · wp_steps
    wp_done

theorem checked_inc_bare_variant_ok (b : BitVec 64) (X : String → Option (State → State)) :
    (checkedIncProg b X).subroutineOk "checked_inc" checkedIncNonZeroSpec := by
  trap_transfer checked_inc_panic_variant_ok b X using
    exact checkedInc_panicsOrTrapsOnly b X

theorem checked_inc_fixed_variant_ok :
    checkedIncFixed.subroutineOk "checked_inc" checkedIncNonZeroSpec := by
  trap_transfer checked_inc_panic_variant_ok 0x500000#64 (fun _ => none) using
    exact checkedInc_panicsOrTrapsOnly_fixed

theorem checked_inc_custom_panic_variant_ok (b : BitVec 64)
    (G X : String → Option (State → State)) :
    (checkedIncCustomPanicProg b G X).subroutineOk "checked_inc" checkedIncNonZeroSpec := by
  trap_transfer checked_inc_panic_variant_ok b X using
    exact checkedInc_panicsOrTrapsOnly_custom b G X

def checkedIncWeakSpec : Spec (BitVec 64) :=
  { pre  := fun x s => ⌜s.readReg64 .x0 = x ∧ x ≠ 0#64⌝
    post := fun x _ sf => ⌜sf.readReg64 .x0 = x + 1#64⌝ }

theorem checked_inc_transfer_and_refine_ok (b : BitVec 64) (X : String → Option (State → State)) :
    subroutine_ok (checkedIncProg b X) ((checkedIncProg b X).fnAddr "checked_inc")
      checkedIncWeakSpec := by
  have h1 : subroutine_ok (checkedIncPanicProg b X) ((checkedIncProg b X).fnAddr "checked_inc")
      checkedIncNonZeroSpec := by
    simpa [Program.subroutineOk, checkedIncPanicProg, wp_unfold] using
      checked_inc_panic_variant_ok b X
  refine h1.of_panicsOrTrapsOnly_mono_sp (checkedInc_panicsOrTrapsOnly b X)
    (fun _ _ => Entails.refl _) (fun x s0 sf _ => ?_)
  dsimp only [checkedIncNonZeroSpec, checkedIncWeakSpec]
  exact Entails.pure_left_only fun h => Entails.pure_right_only h.1 (Entails.refl _)

/-! ### Panicking contract transfer -/

def checkedIncTotalSpec : Spec (BitVec 64) :=
  { pre     := fun x s => ⌜s.readReg64 .x0 = x⌝
    post    := fun x s0 sf => ⌜x ≠ 0#64 ∧ sf.readReg64 .x0 = x + 1#64 ∧ sf.sp = s0.sp ∧
                               CalleeSavedPreserved s0 sf⌝
    onPanic := fun x _ _ => ⌜x = 0#64⌝ }

theorem checked_inc_total_trap_variant_ok (b : BitVec 64) (X : String → Option (State → State)) :
    (checkedIncTrapAndPanicProg b X).subroutineOk "checked_inc" checkedIncTotalSpec := by
  wpp_init x s0
  apply SepWPp.of_sepWP (mid := if x = 0#64 then b + 12#64 else b + 4#64)
  wp_step
  apply SepWP.done (by simp_all) (by simp_all)
  by_cases hx : x = 0#64
  · simp only [hx]
    apply SepWPp.panic (by simp_all)
    · have hext := checkedInc_extern_0c (b := b)
        (H := trapAt (· == "aux_trap") (trapHook "aux fault") (Rust.withPanics X))
      have hpan : (trapAt (· == "aux_trap") (trapHook "aux fault") (Rust.withPanics X))
          panicBoundsSym = some Rust.panicked := by
        simp [trapAt, panicBoundsSym, Rust.withPanics, Rust.isPanicSymbol]
      simp_all
    · intro _
      rw [satisfies_pure_sepConj]
      exact ⟨trivial, by simpa [Rust.panicked] using hpre⟩
  · simp only [hx]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem checked_inc_total_panic_variant_manual (b : BitVec 64)
    (X : String → Option (State → State)) :
    (checkedIncPanicProg b X).subroutineOk "checked_inc" checkedIncTotalSpec := by
  trap_transfer checked_inc_total_trap_variant_ok b X using
    exact checkedInc_trapsOnly b X

/-! ## `hookMap` Integration Tests -/

theorem hookMap_trap_transfer_test (X : String → Option (State → State)) :
    HooksTrapOnly
      (hookMap [("trap_a", trapHook "a"), ("trap_b", trapHook "b")] (Rust.withPanics X))
      (Rust.withPanics X) := by
  refine HooksTrapOnly.hookMap_traps _ ?_ _
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact trapHook_isTrap _

theorem hookMap_congr_transfer_test (f : State → State) (X : String → Option (State → State)) :
    HooksPanicOrTrapOnly
      (hookMap [("helper", f)] (Rust.withPanics X))
      (hookMap [("helper", f)] X) :=
  HooksPanicOrTrapOnly.hookMap [("helper", f)] (HooksPanicOrTrapOnly.withPanics_left X)

/-! ## Structural Descent and `#derive_variant` Tests -/

declare_variant_kind checked_inc_untrap (b : BitVec 64) (X : String → Option (State → State)) :
  checkedIncTrapAndPanicProg b X ==> checkedIncPanicProg b X
  rename "trap_variant" ==> "panic_variant"

declare_variant_kind checked_inc_unpanic (b : BitVec 64) (X : String → Option (State → State)) :
  checkedIncPanicProg b X ==> checkedIncProg b X
  rename "panic_variant" ==> "bare_variant"

#derive_variant (checked_inc_untrap)
  from checked_inc_total_trap_variant_ok
  using fun h => by trap_transfer h using exact checkedInc_trapsOnly _ _

#guard_same_type checked_inc_total_panic_variant_ok checked_inc_total_panic_variant_manual

#derive_variant (checked_inc_unpanic) checked_inc_bare_variant_derived
  from checked_inc_panic_variant_ok
  using fun h => by trap_transfer h using exact checkedInc_panicsOrTrapsOnly _ _

#guard_same_type checked_inc_bare_variant_derived checked_inc_bare_variant_ok

structure CheckedIncBundle (P : Program) : Prop where
  nonZeroOk : P.subroutineOk "checked_inc" checkedIncNonZeroSpec
  guardedOk : ∀ (k : Nat), k > 0 → P.subroutineOk "checked_inc" checkedIncNonZeroSpec

def CheckedIncBundleAlias (P : Program) : Prop := CheckedIncBundle P

def CheckedIncPanicBundle (b : BitVec 64) (X : String → Option (State → State)) : Prop :=
  CheckedIncBundle (checkedIncPanicProg b X)

def CheckedIncBareBundle (b : BitVec 64) (X : String → Option (State → State)) : Prop :=
  CheckedIncBundle (checkedIncProg b X)

variant_map (checked_inc_unpanic) CheckedIncPanicBundle => CheckedIncBareBundle

theorem checked_inc_bundle_panic_variant (b : BitVec 64) (X : String → Option (State → State)) :
    CheckedIncPanicBundle b X :=
  ⟨checked_inc_panic_variant_ok b X, fun _ _ => checked_inc_panic_variant_ok b X⟩

#derive_variant (checked_inc_unpanic) checked_inc_bundle_bare_variant
  from checked_inc_bundle_panic_variant

theorem checked_inc_bundle_bare_expected (b : BitVec 64) (X : String → Option (State → State)) :
    CheckedIncBareBundle b X := by
  trap_transfer checked_inc_bundle_panic_variant b X using
    exact checkedInc_panicsOrTrapsOnly b X

#guard_same_type checked_inc_bundle_bare_variant checked_inc_bundle_bare_expected

/-! ## Negative `#guard_msgs` Tests -/

/--
error: trap_transfer: no transfer lemma applies to
  True
-/
#guard_msgs in
example (h : True) : True := by
  trap_transfer h using exact checkedInc_trapsOnly _ _

/--
error: unknown variant kind `nonexistent_kind`; declare it with `declare_variant_kind`
-/
#guard_msgs in
#derive_variant (nonexistent_kind) bad_kind_thm from checked_inc_panic_variant_ok

/--
error: #derive_variant: the variant kind `checked_inc_untrap` does not change the statement of `Examples.Testing.ProofLib.Variant.checked_inc_bare_variant_ok`
-/
#guard_msgs in
#derive_variant (checked_inc_untrap) bad_no_subterm from checked_inc_bare_variant_ok

/--
error: #guard_same_type: `Examples.Testing.ProofLib.Variant.checked_inc_fixed_variant_ok` and `Examples.Testing.ProofLib.Variant.checked_inc_bare_variant_ok` have different statements:
  checkedIncFixed.subroutineOk "checked_inc" checkedIncNonZeroSpec
is not
  ∀ (b : BitVec 64) (X : String → Option (State → State)),
    (checkedIncProg b X).subroutineOk "checked_inc" checkedIncNonZeroSpec
-/
#guard_msgs in
#guard_same_type checked_inc_fixed_variant_ok checked_inc_bare_variant_ok

/-! ## Axiom Audit -/

/--
info: 'Examples.Testing.ProofLib.Variant.checked_inc_bare_variant_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms checked_inc_bare_variant_ok

/--
info: 'Examples.Testing.ProofLib.Variant.checked_inc_total_panic_variant_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms checked_inc_total_panic_variant_ok

/--
info: 'Examples.Testing.ProofLib.Variant.checked_inc_bundle_bare_variant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms checked_inc_bundle_bare_variant

end Examples.Testing.ProofLib.Variant

end
