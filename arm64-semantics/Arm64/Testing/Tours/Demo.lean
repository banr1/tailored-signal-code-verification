/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Disproof
public import ProofLib.Placed.Fetch
public import Arm64.Testing.Generators.CompiledBinaryFixture
public import Arm64.Testing.Proofs.SpecAdequacyKit

/-!
# Trust Story End-to-End Demo: Specification, Machine-Code Proof, Disproof & Adequacy (`Arm64.Testing.Tours.Demo`)

- **Layer & Role:** Self-contained walkthrough (`Lib::Arm64Testing`, `Role::Test`) for
  `docs/trust-story/demo/README.md` and
  `docs/trust-story/demo/spec-dsl-demo.sh`.
- **Rust Source:** [`Arm64/Testing/Fixtures/compiled-binary/src/functions.rs`](../Fixtures/compiled-binary/src/functions.rs)
  (`arith_shift` and `bad`), compiled with `rustc --release --target aarch64-unknown-linux-gnu`
  and extracted by `rust-obj2lean` into `Arm64/Testing/Generators/CompiledBinaryFixture.lean` (`CompiledBinaryFixture.bin`).
- **What is proved:**
  1. **Specifications (`demoArithShiftSpec` & `demoBadSpec`) and `rfl` macro-expansion check:**
     Shows the exact `Arm64.Spec` record (`pre`, `post`, `onPanic`, `onOom`) that `rust_spec`
     elaborates to for `demoArithShiftSpec` and `demoBadSpec`.
  2. **Binary byte check (`demo_code` & `demoArithShift_code`):** Checks by kernel evaluation
     that `Arm64/Testing/Generators/CompiledBinaryFixture.bin` contains the instruction words of
     `demoArithShiftCode` and `demoBadCode` at their symbol-table offsets (`1588` and `1720`), and
     lifts `DemoArithShiftCodeAt` to every valid placement `pl` (`fixturePlacedLib.Placeable pl`).
  3. **Total-correctness Hoare triple (`demoArithShift_ok`):** Proves `subroutineOk` for
     `examples::functions::arith_shift` across every valid placement `pl` of `fixturePlacedLib`.
  4. **Machine-code disproof (`demoBad_not_subroutine_ok`):** Disproves `subroutine_ok` for
     `examples::functions::bad` (`fn bad(x: u64) { assert!(x == 0) }`) under `demoBadSpec`:
     calling `bad(1)` takes the `cbnz x0` branch and calls `core::panicking::panic`, transitioning
     to `.Panicked` where `demoBadSpec.onPanic = ⌜False⌝`.
  5. **Operational adequacy (`demoArithShift_adequacy`):** Specializes
     [`Arm64/Testing/Proofs/SpecAdequacyKit.lean`](../Proofs/SpecAdequacyKit.lean) to
     `demoArithShift_ok`, stating the verified guarantee of the compiled Rust binary directly in
     terms of `fixturePlacedLib.Placeable pl`, `Arm64.Steps`, `State.readReg64`, and `Memory.read8`
     with zero separation-logic definitions in the theorem statement.
  6. **Kernel axiom check (`#print axioms`):** Confirms all theorems depend only on Lean's three
     standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

@[expose] public section

namespace Arm64.Testing.Tours.Demo

open Arm64
open ProofLib
open ProofLib.Disproof
open Testing.Generators
open Arm64.Testing.SpecAdequacyTour

set_option maxRecDepth 200000

/-! ## 1. Specifications (`examples::functions::arith_shift` & `examples::functions::bad`)

Rust source (`Arm64/Testing/Fixtures/compiled-binary/src/functions.rs:95-98`):
```rust
#[inline(never)]
pub fn arith_shift(x: u64) -> u64 {
    (x.wrapping_add(42)).wrapping_mul(3)
}
```
`rustc -O` algebraic-simplifies `(x + 42) * 3` into `3 * x + 126` (`0x7e`), emitting 3 AArch64
instructions (12 bytes at offset `1588` / `0x634` of `CompiledBinaryFixture.bin`):
- `+0x00`: `8b000408` — `add x8, x0, x0, lsl #1` (`x8 := x0 + 2 * x0 = 3 * x0`)
- `+0x04`: `9101f900` — `add x0, x8, #0x7e` (`x0 := x8 + 126`)
- `+0x08`: `d65f03c0` — `ret`
-/

def demoArithShiftCode : FnCode :=
  .ofFn "examples::functions::arith_shift" "8b000408 9101f900 d65f03c0"

abbrev DemoArithShiftCodeAt (prog : Program) : Prop :=
  demoArithShiftCode.holds prog

/-- Hoare specification for `examples::functions::arith_shift`:
    given `x : u64` in `X0`, returns `(x + 42) * 3` (mod 2^64) in `X0` without faulting or panicking. -/
rust_spec demoArithShiftSpec (x : u64) : u64
  returns (x + 42#64) * 3#64

/-!
Rust source (`Arm64/Testing/Fixtures/compiled-binary/src/functions.rs:191-193`):
```rust
#[inline(never)]
pub fn bad(x: u64) {
    assert!(x == 0)
}
```
`rustc -O` emits 10 AArch64 instructions (40 bytes at offset `1720` / `0x6b8` of `CompiledBinaryFixture.bin`):
- `+0x00`: `b5000040` — `cbnz x0, +0x8` (branches to panic block when `x ≠ 0`)
- `+0x04`: `d65f03c0` — `ret` (normal return when `x = 0`)
- `+0x08`: `a9bf7bfd` — `stp x29, x30, [sp, #-0x10]!`
- `+0x0c`: `910003fd` — `mov x29, sp`
- `+0x10..+0x20`: `adrp`/`add`/`mov` preparing panic message arguments in `x0`, `w1`, `x2`
- `+0x24`: `94000081` — `bl 0x8e0 <core::panicking::panic>`
-/

def demoBadCode : FnCode :=
  .ofFn "examples::functions::bad"
    "b5000040 d65f03c0 a9bf7bfd 910003fd b0000000 91000000 b0000002 91010042 52800301 94000081"

abbrev DemoBadCodeAt (prog : Program) : Prop :=
  demoBadCode.holds prog

/-- Naive unguarded specification for `examples::functions::bad` claiming it returns normally
    for every `x : u64` (even when given the 16-byte stack frame `[sp0 - 16, sp0)` needed by
    `stp x29, x30, [sp, #-0x10]!`). Disproved for `x = 1` below. -/
rust_spec demoBadSpec (x : u64) (ghost sp0 : ptr)
  requires_cond s0.sp = sp0
  requires memRegion (sp0 - 16#64) 16
  ensures  memRegion (sp0 - 16#64) 16

/-- Entry address `0x106b8` (`bad` at offset `0x6b8` above base `0x10000`) and relative stub
    offset `0x228` (`0x8e0 - 0x6b8`, so `bl +0x204` from `+0x24` lands at `0x108e0`). -/
abbrev badEntry   : BitVec 64 := 0x106b8#64
abbrev badStubOff : Nat       := 0x228

/-- Extracted machine code of `examples::functions::bad` (`demoBadCode.hex`, verified against
    `fixturePlacedLib` by `demo_code`) with `core::panicking::panic` mapped to `Rust.panicked`. -/
def demoBadProg : Program :=
  { Program.ofWords badEntry demoBadCode.hex with
    stubs := [("core::panicking::panic", badStubOff)]
    externs := fun name => if name == "core::panicking::panic" then some Rust.panicked else none }

/-- Bundled `FnCode` specification for the demo functions. -/
def demoCodeBundle : CodeBundle :=
  [demoArithShiftCode, demoBadCode]

/-! ## 2. Elaborated `Spec` Records (Checked by `rfl`)

As shown in general in [`Arm64/Testing/Tours/SpecAdequacyTour.lean`](SpecAdequacyTour.lean),
the `rust_spec` macro is syntactic sugar for an `Arm64.Spec` structure. A reviewer can inspect the
elaborated `pre`, `post`, `onPanic`, and `onOom` fields directly by `rfl`: -/

example (x : BitVec 64) (s0 sf : State) :
    demoArithShiftSpec.pre x s0 = ⌜s0.readReg64 .x0 = x⌝ ∧
    demoArithShiftSpec.post x s0 sf = ⌜sf.readReg64 .x0 = (x + 42#64) * 3#64⌝ ∧
    demoArithShiftSpec.onPanic x s0 sf = ⌜False⌝ ∧
    demoArithShiftSpec.onOom x s0 sf = ⌜False⌝ := ⟨rfl, rfl, rfl, rfl⟩

example (x sp0 : BitVec 64) (s0 sf : State) :
    demoBadSpec.pre (x, sp0) s0 =
      (⌜s0.readReg64 .x0 = x ∧ s0.sp = sp0⌝ ∗ memRegion (sp0 - 16#64) 16) ∧
    demoBadSpec.post (x, sp0) s0 sf =
      memRegion (sp0 - 16#64) 16 ∧
    demoBadSpec.onPanic (x, sp0) s0 sf = ⌜False⌝ ∧
    demoBadSpec.onOom (x, sp0) s0 sf = ⌜False⌝ := ⟨rfl, rfl, rfl, rfl⟩

/-! ## 3. Connecting the Proof to `CompiledBinaryFixture.bin` Bytes (`rfl` Validation)

To make sure `.hasCodeBundle` and `fixturePlacedLib.Placeable pl` do not have to be trusted as black
boxes, we check every step of how `fixturePlacedLib` (`Arm64/Testing/Generators/CompiledBinaryFixture.lean`,
whose `text.code` field is `include_bytes% "CompiledBinaryFixture.bin" 0 2272`) connects to the proof by `rfl`: -/

-- (a) Symbol offsets and panic extern in `fixturePlacedLib`:
example : Obj.lookup "examples::functions::arith_shift" fixturePlacedLib.text.symbols = some 1588 := rfl
example : Obj.lookup "examples::functions::bad"         fixturePlacedLib.text.symbols = some 1720 := rfl
example : "_RNvNtCskxtBwYRO61I_4core9panicking5panic" ∈ fixturePlacedLib.text.externs := by decide

-- (b) Raw byte slices of `fixturePlacedLib.text.code` (`CompiledBinaryFixture.bin`) at offsets 1588 and 1720
--     match the extracted `.text` bytes byte-for-byte:
example : (fixturePlacedLib.text.code.drop 1588).take 12 =
    [0x08#8, 0x04#8, 0x00#8, 0x8b#8,   -- 0x8b000408: add x8, x0, x0, lsl #1
     0x00#8, 0xf9#8, 0x01#8, 0x91#8,   -- 0x9101f900: add x0, x8, #0x7e
     0xc0#8, 0x03#8, 0x5f#8, 0xd6#8]   -- 0xd65f03c0: ret
  := rfl

example : (fixturePlacedLib.text.code.drop 1720).take 40 =
    [0x40#8, 0x00#8, 0x00#8, 0xb5#8,   -- 0xb5000040: cbnz x0, +0x8
     0xc0#8, 0x03#8, 0x5f#8, 0xd6#8,   -- 0xd65f03c0: ret
     0xfd#8, 0x7b#8, 0xbf#8, 0xa9#8,   -- 0xa9bf7bfd: stp x29, x30, [sp, #-0x10]!
     0xfd#8, 0x03#8, 0x00#8, 0x91#8,   -- 0x910003fd: mov x29, sp
     0x00#8, 0x00#8, 0x00#8, 0x90#8,   -- 0x90000000: adrp x0, ...
     0x00#8, 0x00#8, 0x00#8, 0x91#8,   -- 0x91000000: add x0, x0, #0x0
     0x02#8, 0x00#8, 0x00#8, 0x90#8,   -- 0x90000002: adrp x2, ...
     0x42#8, 0x00#8, 0x00#8, 0x91#8,   -- 0x91000042: add x2, x2, #0x0
     0x01#8, 0x03#8, 0x80#8, 0x52#8,   -- 0x52800301: mov w1, #0x18
     0x00#8, 0x00#8, 0x00#8, 0x94#8]   -- 0x94000000: bl <core::panicking::panic>
  := rfl

-- (c) What `.hasCodeBundle` and `DemoArithShiftCodeAt` (`FnCode.holds`) unfold to by `rfl`:
--     `DemoArithShiftCodeAt prog` asserts that at `off := prog.fnOff "examples::functions::arith_shift"`,
--     reading the three 32-bit little-endian words from `prog.code` (`prog.readWordOff (off + 4 * i)`)
--     yields `[0x8b000408#32, 0x9101f900#32, 0xd65f03c0#32]` and no hook intercepts `[off, off + 12)`.
example (prog : Program) :
    prog.hasCodeBundle demoCodeBundle =
      (DemoArithShiftCodeAt prog ∧ DemoBadCodeAt prog) := rfl

example (prog : Program) :
    DemoArithShiftCodeAt prog =
      (let off := prog.fnOff "examples::functions::arith_shift"
       off + 12 ≤ 2 ^ 64 ∧
       (∀ (i : Nat) (hi : i < 3),
         prog.readWordOff (off + 4 * i) =
           some ([0x8b000408#32, 0x9101f900#32, 0xd65f03c0#32][i]'hi)) ∧
       prog.hookFree off 12) := rfl

-- (d) How `fixturePlacedLib.program pl Rust.withPanics` resolves the symbol table and entry addresses
--     to `pl.base + 1588#64` (`0x634`) and `pl.base + 1720#64` (`0x6b8`):
theorem demo_placeable_unpack {pl : Obj.Placement} :
    (fixturePlacedLib.program pl Rust.withPanics).symbols = fixturePlacedLib.text.symbols ∧
    (fixturePlacedLib.program pl Rust.withPanics).fnAddr "examples::functions::arith_shift" =
      pl.base + 1588#64 ∧
    (fixturePlacedLib.program pl Rust.withPanics).fnAddr "examples::functions::bad" =
      pl.base + 1720#64 :=
  ⟨rfl,
   (Obj.PlacedLib.fnAddr_program (lib := fixturePlacedLib) (pl := pl) (off := 1588) rfl).1,
   (Obj.PlacedLib.fnAddr_program (lib := fixturePlacedLib) (pl := pl) (off := 1720) rfl).1⟩

private theorem patchRelocs_nil (words : List (BitVec 32)) (a : BitVec 64)
    (resolve : String → BitVec 64) :
    Obj.patchRelocs [] words a resolve = words := by
  unfold Obj.patchRelocs
  have h : ∀ (ws : List (BitVec 32)) (k : Nat),
      (ws.zipIdx k).map (fun (w, _) => w) = ws := by
    intro ws
    induction ws with
    | nil => intro _; rfl
    | cons w ws ih => intro k; simp [List.zipIdx_cons, ih]
  exact h words 0

private theorem fnOff_program_of_lookup {lib : Obj.PlacedLib} {pl : Obj.Placement}
    {X O : String → Option (State → State)} {svc : State → State}
    {name : String} {fo : Nat} (h : Obj.lookup name lib.text.symbols = some fo) :
    (lib.program pl X O svc).fnOff name = fo := by
  have h' : (lib.text.symbols.find? (·.1 == name)).map (·.2) = some fo := h
  have hs : (lib.program pl X O svc).symbols = lib.text.symbols := rfl
  cases hf : lib.text.symbols.find? (·.1 == name) with
  | none => rw [hf] at h'; simp at h'
  | some p =>
    rw [hf] at h'
    have hp : p.2 = fo := by simpa using h'
    simp [Program.fnOff, Program.findSymbol?, hs, hf, Option.orElse, hp]

/-- Placement-independent check that `fc` is a relocation-free function in `lib.text`. -/
def checkPlacedFnCode (lib : Obj.PlacedLib) (fc : FnCode) : Bool :=
  match Obj.lookup fc.fnName lib.text.symbols with
  | none => false
  | some fo =>
    (match fc.pin with
     | .none => true
     | .off off => fo == off
     | .addr _ => false) &&
    decide (fo + 4 * fc.hex.length ≤ lib.text.code.length) &&
    lib.text.checkSegment fo fc.hex []

theorem holds_program_of_check {lib : Obj.PlacedLib} {pl : Obj.Placement} {fc : FnCode}
    {X : String → Option (State → State)} {svc : State → State}
    (hP : lib.Placeable pl) (hchk : checkPlacedFnCode lib fc = true) :
    fc.holds (lib.program pl X (fun _ => none) svc) := by
  unfold checkPlacedFnCode at hchk
  cases hsym : Obj.lookup fc.fnName lib.text.symbols with
  | none => rw [hsym] at hchk; contradiction
  | some fo =>
    rw [hsym] at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨hpin, hlen⟩, hseg⟩ := hchk
    have hfnOff : (lib.program pl X (fun _ => none) svc).fnOff fc.fnName = fo :=
      fnOff_program_of_lookup hsym
    have hwords := (Obj.CodeBlock.hasWords_of_checkSegment
      (prog := lib.program pl X (fun _ => none) svc) hP.text rfl rfl hseg
      (Obj.PlacedLib.hookFree_program_noOverrides (X := X) (svc := svc) hP.text hlen)).1
    rw [patchRelocs_nil] at hwords
    unfold Program.hasWords at hwords
    have hnw := hP.text.no_wrap
    have hpos : 0 < fc.hex.length := by
      simp only [Obj.CodeBlock.checkSegment, Bool.and_eq_true, decide_eq_true_eq] at hseg
      exact hseg.1.1.1.2
    have hfo_lt : fo < 2 ^ 64 := by omega
    have hoff : (pl.base + BitVec.ofNat 64 fo - (lib.program pl X (fun _ => none) svc).base).toNat = fo := by
      rw [Obj.PlacedLib.program_base, Program.add_ofNat_sub_self, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hfo_lt]
    rw [hoff] at hwords
    have hcodeAt : (lib.program pl X (fun _ => none) svc).codeAt fc.fnName fc.hex := by
      unfold Program.codeAt
      rwa [hfnOff]
    rcases fc with ⟨fnName, hex, pin⟩
    cases pin with
    | none => exact hcodeAt
    | off off =>
      simp only [beq_iff_eq] at hpin
      subst hpin
      exact ⟨hfnOff, hcodeAt⟩
    | addr _ => simp at hpin

/-- Canonical placement of `fixturePlacedLib` at base `0x10000#64`, matching `badEntry` (`0x106b8#64`),
    `badStubOff` (`0x228`, so `core::panicking::panic` is at `0x108e0#64`), and the `.rodata`
    panic location descriptors at `0x11000#64` and `0x11040#64`. -/
def demoPlacement : Obj.Placement where
  base := 0x10000#64
  ρ name :=
    if name == "examples:.rodata..Lanon.0" then 0x11000#64
    else if name == "examples:.rodata..Lanon.2" then 0x11040#64
    else if name == "examples:.rodata..Lanon.4" then 0x11080#64
    else if name == "examples:.rodata..Lanon.5" then 0x110c0#64
    else if name == "examples:.rodata..Lanon.6" then 0x11100#64
    else if name == "examples:.rodata.str1.1+0x0" then 0x11140#64
    else if name == "examples:.rodata.str1.1+0x11" then 0x11180#64
    else if name == "_RNvNtCskxtBwYRO61I_4core9panicking5panic" then 0x108e0#64
    else if name == "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" then 0x108e4#64
    else 0x20000#64

private instance (t : BitVec 64) : Decidable (Obj.Abs32InRange t) :=
  inferInstanceAs (Decidable (_ ∧ _))
private instance (p t : BitVec 64) : Decidable (Obj.Prel32InRange p t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem demoPlacement_placeable : fixturePlacedLib.Placeable demoPlacement :=
  ⟨Obj.CodeBlock.placeable_of_checkPlaceable (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Under the canonical placement `demoPlacement`, the placed program
    `fixturePlacedLib.program demoPlacement Rust.withPanics` satisfies the full `demoCodeBundle`
    (both `demoArithShiftCode` and all 10 words of `demoBadCode`). -/
theorem demo_code :
    (fixturePlacedLib.program demoPlacement Rust.withPanics).hasCodeBundle demoCodeBundle := by
  arm64_decide_code

/-- For every valid placement `pl` of `fixturePlacedLib` (`fixturePlacedLib.Placeable pl`), the placed
    program `fixturePlacedLib.program pl Rust.withPanics` satisfies `DemoArithShiftCodeAt`. -/
theorem demoArithShift_code {pl : Obj.Placement} (h : fixturePlacedLib.Placeable pl) :
    DemoArithShiftCodeAt (fixturePlacedLib.program pl Rust.withPanics) :=
  holds_program_of_check h (by decide +kernel)

/-! ## 4. Machine-Code Verification of `arith_shift` (`subroutineOk`) -/

/-- Position-independent proof of `examples::functions::arith_shift`. -/
theorem demoArithShift_ok_abstract (prog : Program) (h_code : DemoArithShiftCodeAt prog) :
    prog.subroutineOk "examples::functions::arith_shift" demoArithShiftSpec := by
  wp_init x s0
  wp_steps
  wp_done

/-- **Placement-level theorem for `arith_shift`:** in every valid placement `pl` of `fixturePlacedLib`,
    calling `examples::functions::arith_shift` with `x` in `X0` terminates normally at `X30`,
    preserves `SP` and callee-saved registers `X19`–`X29`, and returns `(x + 42) * 3` in `X0`. -/
theorem demoArithShift_ok (pl : Obj.Placement) (h : fixturePlacedLib.Placeable pl) :
    (fixturePlacedLib.program pl Rust.withPanics).subroutineOk
      "examples::functions::arith_shift" demoArithShiftSpec :=
  demoArithShift_ok_abstract _ (demoArithShift_code h)

def rustSliceIndexCode : FnCode :=
  .ofFn "examples::functions::slice_index" "f8617800 d65f03c0"

abbrev RustSliceIndexCodeAt (prog : Program) : Prop :=
  rustSliceIndexCode.holds prog

rust_spec rustSliceIndexSpec (ptr : ptr) (idx : usize) (ghost elem : u64) : u64
  preserves (ptr + (idx <<< 3)) ↦₆₄ elem
  returns   elem

theorem rustSliceIndex_code {pl : Obj.Placement} (h : fixturePlacedLib.Placeable pl) :
    RustSliceIndexCodeAt (fixturePlacedLib.program pl Rust.withPanics) :=
  holds_program_of_check h (by decide +kernel)

theorem rustSliceIndex_ok_abstract (prog : Program) (h_code : RustSliceIndexCodeAt prog) :
    prog.subroutineOk "examples::functions::slice_index" rustSliceIndexSpec := by
  wp_init a s0
  wp_steps
  wp_done

theorem rustSliceIndex_ok (pl : Obj.Placement) (h : fixturePlacedLib.Placeable pl) :
    (fixturePlacedLib.program pl Rust.withPanics).subroutineOk
      "examples::functions::slice_index" rustSliceIndexSpec :=
  rustSliceIndex_ok_abstract _ (rustSliceIndex_code h)

def rustMemSwapCode : FnCode :=
  .ofFn "examples::functions::mem_swap" "f9400028 f9400009 f9000008 f9000029 d65f03c0"

abbrev RustMemSwapCodeAt (prog : Program) : Prop :=
  rustMemSwapCode.holds prog

rust_spec rustMemSwapSpec (ptrA : ptr) (ptrB : ptr) (ghost valA : u64) (ghost valB : u64)
  requires (ptrA ↦₆₄ valA) ∗ (ptrB ↦₆₄ valB)
  ensures  (ptrA ↦₆₄ valB) ∗ (ptrB ↦₆₄ valA)

theorem rustMemSwap_code {pl : Obj.Placement} (h : fixturePlacedLib.Placeable pl) :
    RustMemSwapCodeAt (fixturePlacedLib.program pl Rust.withPanics) :=
  holds_program_of_check h (by decide +kernel)

theorem rustMemSwap_ok_abstract (prog : Program) (h_code : RustMemSwapCodeAt prog) :
    prog.subroutineOk "examples::functions::mem_swap" rustMemSwapSpec := by
  wp_init a s0
  wp_steps
  wp_done

theorem rustMemSwap_ok (pl : Obj.Placement) (h : fixturePlacedLib.Placeable pl) :
    (fixturePlacedLib.program pl Rust.withPanics).subroutineOk
      "examples::functions::mem_swap" rustMemSwapSpec :=
  rustMemSwap_ok_abstract _ (rustMemSwap_code h)

/-! ## 5. Machine-Code Disproof of `bad` (`¬ subroutine_ok`)

For `pub fn bad(x: u64) { assert!(x == 0) }`, we construct a concrete counterexample state `badS0`
with `X0 = 1#64` and a mapped 16-byte stack frame `[0x30000, 0x30010)`. Stepping the 10 extracted
instructions of `demoBadCode` takes the `cbnz x0` branch (`+0x00 -> +0x08`), spills `x29, x30`,
sets up the panic arguments, and jumps via `bl` (`+0x24`) to `core::panicking::panic` (`+0x228`),
which transitions to `ExecStatus.Panicked` and refutes `subroutine_ok`. -/

/-- Mapped 16-byte stack frame `[0x30000, 0x30010)` (`sp0 = 0x30010`) for the `bad(1)` counterexample. -/
abbrev badStackBase : BitVec 64 := 0x30000#64
abbrev badSp0       : BitVec 64 := 0x30010#64

def badRegions : List DisproofRegion :=
  [.rwRegion badStackBase 16]

def badS0 : State :=
  mkDisproofState demoBadProg badEntry
    (sp0 := badSp0)
    (regs := [(.x0, 1#64)])
    (rs := badRegions)

/-- Execution of `prog` starting from state `s` reaches a terminal `.Panicked` state. -/
def ReachesPanicked (prog : Program) (s : State) : Prop :=
  ∃ sf, Steps prog s sf ∧ sf.status = .Panicked

theorem ReachesPanicked.of_exec_step {prog : Program} {s : State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hcode : prog.CodeLoaded s.mem)
    (hsome : (prog.fetch s.pc).isSome = true := by with_unfolding_all decide)
    (hrest : prog.CodeLoaded (ProofLib.stepInst prog s).mem →
      ReachesPanicked prog (ProofLib.stepInst prog s)) :
    ReachesPanicked prog s := by
  obtain ⟨sf, hsteps, hpan⟩ := hrest (Program.CodeLoaded.stepInst hcode)
  rw [stepInst_eq_execInst_fetchInstD hsome] at hsteps
  exact ⟨sf, .step (Step.exec hrun (Program.fetchMem_of_fetch hcode (fetch_eq_some_fetchInstD hsome))) hsteps, hpan⟩

theorem ReachesPanicked.of_extern_panic {prog : Program} {s : State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hextern : prog.externAt? s.pc = some Rust.panicked := by with_unfolding_all rfl) :
    ReachesPanicked prog s :=
  ⟨Rust.panicked s, .step (Step.extern hrun hextern (Memory.KeepsFrozen.refl _) rfl) (.refl _), rfl⟩

/-- **Disproof of `subroutine_ok` for `bad(x: u64) { assert!(x == 0) }`:**
    when `x = 1#64`, `bad` branches past `ret` (`cbnz x0, +0x8`) and invokes `core::panicking::panic`,
    reaching `sf.status = .Panicked` and violating `demoBadSpec` (`onPanic = ⌜False⌝`). -/
theorem demoBad_not_subroutine_ok :
    ¬ subroutine_ok demoBadProg badEntry demoBadSpec := by
  have hcode : demoBadProg.CodeLoaded badS0.mem :=
    mkDisproofState_codeLoaded demoBadProg badEntry
      (sp0 := badSp0) (regs := [(.x0, 1#64)]) (rs := badRegions)
  have hsat_raw := mkDisproofState_satisfies demoBadProg badEntry
    (sp0 := badSp0) (regs := [(.x0, 1#64)]) (rs := badRegions)
  have hpre : badS0.mem ⊨ demoBadSpec.pre (1#64, badSp0) badS0 ∗ SepProp.emp := by
    rw [sepConj_emp]
    unfold demoBadSpec
    rw [satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl⟩, hsat_raw⟩
  -- 9 instructions along `x0 = 1` path: `cbnz`, `stp`, `mov x29`, 2×(`adrp`, `add`), `mov w1`, `bl`, then panic hook
  have ⟨sf, hsteps, hpan⟩ : ReachesPanicked demoBadProg badS0 := by
    refine ReachesPanicked.of_exec_step (hcode := hcode) (hrest := fun hcode1 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode1) (hrest := fun hcode2 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode2) (hrest := fun hcode3 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode3) (hrest := fun hcode4 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode4) (hrest := fun hcode5 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode5) (hrest := fun hcode6 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode6) (hrest := fun hcode7 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode7) (hrest := fun hcode8 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode8) (hrest := fun _ => ?_)
    exact ReachesPanicked.of_extern_panic
  have honpanic_false :
      ¬ (sf.mem ⊨ demoBadSpec.onPanic (1#64, badSp0) badS0 sf ∗ SepProp.emp) := by
    rw [sepConj_emp]
    intro h
    simp [demoBadSpec] at h
  exact not_subroutine_ok_of_panic_post_false
    (1#64, badSp0) SepProp.emp
    (mkDisproofState_aapcsEntry demoBadProg badEntry
      (sp0 := badSp0) (regs := [(.x0, 1#64)]) (rs := badRegions))
    hcode hpre hsteps hpan honpanic_false

/-! ## 6. Operational Adequacy of `demoArithShiftSpec` & `demoArithShift_ok` -/

/-- **Adequacy of `demoArithShiftSpec`.** Any program `prog` and entry address `entry` satisfying
    `subroutine_ok prog entry demoArithShiftSpec` terminates without fault, halt, panic, exit, or
    OOM before return, returns `(x + 42) * 3` (mod 2^64) in `X0`, preserves `SP` and callee-saved
    registers `X19`–`X29`, and leaves every readable byte of memory unchanged. -/
theorem demoArithShiftSpec_adequacy (prog : Program) (entry : BitVec 64) :
    subroutine_ok prog entry demoArithShiftSpec →
    ∀ (s₀ : State) (x : BitVec 64),
      -- ENTRY CONDITIONS: running at `entry`, 16-byte aligned SP, code loaded, X0 = x:
      s₀.status = .Running →
      s₀.pc = entry →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = x →
      -- CONCLUSION: execution reaches a return state s' via the trusted small-step semantics
      ∃ s' : State,
        Steps prog s₀ s' ∧
        -- that returned to the caller's link register X30 in Running status,
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        -- with no fault, halt, panic, exit, or OOM before s' (every state reached from s₀ is
        -- either Running or comes at/after the return state s'),
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        -- X0 holds (x + 42) * 3 (mod 2^64),
        s'.readReg64 .x0 = (x + 42#64) * 3#64 ∧
        -- SP and AAPCS64 callee-saved registers X19..X29 are preserved,
        s'.sp = s₀.sp ∧
        (∀ r ∈ calleeSavedRegs, s'.readReg64 r = s₀.readReg64 r) ∧
        -- and every readable non-`MADV_FREE` byte in memory is unchanged (frame property with empty footprint).
        (∀ a : BitVec 64, (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) := by
  intro h_ok s₀ x h_run h_pc h_sp h_code h_x0
  have hpre_eq : demoArithShiftSpec.pre x s₀ = (⌜s₀.readReg64 .x0 = x⌝ ∗ SepProp.emp) := by
    rw [sepConj_emp]; rfl
  have hpre : ∃ h, demoArithShiftSpec.pre x s₀ h ∧ h.Matches s₀.mem := by
    rw [hpre_eq]
    have h0 := bytes_heap s₀.mem 0#64 0 (by decide) (fun _ h => nomatch h)
    rw [Memory.readBytes, ProofLib.pointsToBytes_nil] at h0
    exact heap_pure_sepConj h_x0 h0
  have hsupp : SupportedIn (demoArithShiftSpec.pre x s₀) (fun _ => False) := by
    rw [hpre_eq]
    exact supp_pure_sepConj (supp_emp _)
  obtain ⟨s', hsteps, hst, hpc, hsafe, hsp, hcs, hpost⟩ :=
    subroutine_ok_adequacy h_ok (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      x (fun _ => False) s₀ h_pc h_run (spAligned_of h_sp) h_code hpre hsupp
  have hpost_eq : demoArithShiftSpec.post x s₀ s' =
      (⌜s'.readReg64 .x0 = (x + 42#64) * 3#64⌝ ∗ SepProp.emp) := by
    rw [sepConj_emp]; rfl
  rw [hpost_eq] at hpost
  obtain ⟨hret, hpost_frame⟩ := sat_pure_sepConj hpost
  refine ⟨s', hsteps, hst, hpc, hsafe, hret, hsp, calleeSaved_of hcs, ?_⟩
  intro a hr hlf
  exact frame_preserved hpost_frame a not_false hr hlf

/-- **End-to-end expanded correctness theorem for `examples::functions::arith_shift` in `fixturePlacedLib`.**
    Combines `demoArithShift_ok` with `demoArithShiftSpec_adequacy` to state the verified guarantee
    of the compiled Rust binary directly in terms of `fixturePlacedLib.Placeable pl`, `Arm64.Steps`,
    `State.readReg64`, and `Memory.read8` — with zero separation-logic definitions in the theorem statement. -/
theorem demoArithShift_adequacy (pl : Obj.Placement) (h : fixturePlacedLib.Placeable pl) :
    let prog := fixturePlacedLib.program pl Rust.withPanics
    ∀ (s₀ : State) (x : BitVec 64),
      s₀.status = .Running →
      s₀.pc = prog.fnAddr "examples::functions::arith_shift" →
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 →
      prog.CodeLoaded s₀.mem →
      s₀.readReg64 .x0 = x →
      ∃ s' : State,
        Steps prog s₀ s' ∧
        s'.status = .Running ∧
        s'.pc = s₀.readReg64 .x30 ∧
        (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) ∧
        s'.readReg64 .x0 = (x + 42#64) * 3#64 ∧
        s'.sp = s₀.sp ∧
        (∀ r ∈ calleeSavedRegs, s'.readReg64 r = s₀.readReg64 r) ∧
        (∀ a : BitVec 64, (s₀.mem.perm a).r = true → s₀.mem.isLazyFree a = false →
          s'.mem.read8 a = s₀.mem.read8 a) :=
  demoArithShiftSpec_adequacy _ _ (demoArithShift_ok pl h)

/-! ## 7. Kernel Axiom Verification -/

/--
info: 'Arm64.Testing.Tours.Demo.demoArithShift_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms demoArithShift_ok

/--
info: 'Arm64.Testing.Tours.Demo.demoBad_not_subroutine_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms demoBad_not_subroutine_ok

/--
info: 'Arm64.Testing.Tours.Demo.demoArithShift_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms demoArithShift_adequacy

end Arm64.Testing.Tours.Demo
