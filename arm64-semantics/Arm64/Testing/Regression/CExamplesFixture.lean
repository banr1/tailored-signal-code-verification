/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.ObjectLoad
public import ProofLib.GenDecodes
public import ProofLib.PrologueFrame
public import ProofLib.GenPlacedFetches

/-!
# Synthetic C and Placed-Library Fixtures

Self-contained three-function fixture (`c_arith_shift`, `c_max_u64`, `c_swap_u64`) with companion
`c_spec` contracts, plus a minimal 32-byte-frame `Obj.PlacedLib` (`frame32Lib`) for code-lookup,
load-address, and symbol-index regression tests.
-/

@[expose] public section

namespace Testing.CExamplesFixture

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

def cExamplesObj : Obj.ObjectInfo :=
  { name := "c_examples"
    fns :=
      [ ("c_arith_shift",
         [0x08#8, 0x04#8, 0x00#8, 0x8b#8, 0x00#8, 0xf9#8, 0x01#8, 0x91#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8])
      , ("c_max_u64",
         [0x1f#8, 0x00#8, 0x01#8, 0xeb#8, 0x00#8, 0x80#8, 0x81#8, 0x9a#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8])
      , ("c_swap_u64",
         [0x28#8, 0x00#8, 0x40#8, 0xf9#8, 0x09#8, 0x00#8, 0x40#8, 0xf9#8, 0x08#8, 0x00#8, 0x00#8, 0xf9#8,
          0x29#8, 0x00#8, 0x00#8, 0xf9#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8]) ] }

def cExamplesImage : Obj.LinkedImage :=
  { code :=
      [0x08#8, 0x04#8, 0x00#8, 0x8b#8, 0x00#8, 0xf9#8, 0x01#8, 0x91#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8,
       0x1f#8, 0x00#8, 0x01#8, 0xeb#8, 0x00#8, 0x80#8, 0x81#8, 0x9a#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8,
       0x28#8, 0x00#8, 0x40#8, 0xf9#8, 0x09#8, 0x00#8, 0x40#8, 0xf9#8, 0x08#8, 0x00#8, 0x00#8, 0xf9#8,
       0x29#8, 0x00#8, 0x00#8, 0xf9#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8]
    dataOff := 0x1000
    data := []
    gotOff := 0x1000
    symbols := [("c_arith_shift", 0x0), ("c_max_u64", 0xc), ("c_swap_u64", 0x18)]
    stubs := []
    objects := [cExamplesObj] }

abbrev cExamplesCodeTextEnd : Nat := 44

def cExamplesCode : Program := cExamplesImage.toProgram

def cExamplesCode_tree : WordTree := word_tree_of% cExamplesCode

theorem cExamplesCode_code_eq : cExamplesCode.code = cExamplesCode_tree.toBytes := by rfl_kernel

theorem cExamplesCode_tree_size : cExamplesCode_tree.checkSize? = some 11 := by rfl_kernel

theorem cExamplesCode_noStubBefore : noStubBefore 44 cExamplesCode.stubs = true := by rfl_kernel

theorem cExamplesCode_fetch_at {off : Nat} {inst : Instr}
    (h : cExamplesCode_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64 := by decide) :
    cExamplesCode.fetch (BitVec.ofNat 64 off) = some inst := by
  have h' := fetch_of_wordTree 11 cExamplesCode_code_eq cExamplesCode_tree_size h hoff
  rwa [show cExamplesCode.base = 0#64 from rfl, BitVec.zero_add] at h'

theorem cExamplesCode_fetch_rebase {b : BitVec 64} {X O : String → Option (State → State)}
    {off : Nat} {inst : Instr}
    (h : cExamplesCode_tree.fetchDecodeAt off = some inst)
    (hhook : (cExamplesCode.rebase b X O).hookAtOff? off = none)
    (hoff : off < 2 ^ 64 := by decide) :
    (cExamplesCode.rebase b X O).fetch (b + BitVec.ofNat 64 off) = some inst :=
  (Program.fetch_rebase_eq_of_hookAtOff? rfl (fun _ => rfl) (fun _ => rfl) hoff hhook).trans
    (cExamplesCode_fetch_at h hoff)

theorem cExamplesCode_fetch_rebase_text {b : BitVec 64} {X : String → Option (State → State)}
    {off : Nat} {inst : Instr}
    (h : cExamplesCode_tree.fetchDecodeAt off = some inst)
    (htext : off < 44 := by decide)
    (hoff : off < 2 ^ 64 := by decide) :
    (cExamplesCode.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :=
  cExamplesCode_fetch_rebase h (hookAtOff?_eq_none_of_noStubBefore cExamplesCode_noStubBefore (fun _ => rfl) htext) hoff

theorem cExamplesCode_fetch_fnAddr {b : BitVec 64} {H : String → Option (State → State)}
    {name : String} {off k : Nat} {inst : Instr}
    (hfn : cExamplesCode.fnOff name = off) (htext : off + k < 44)
    (h : cExamplesCode_tree.fetchDecodeAt (off + k) = some inst)
    (hoff : off + k < 2 ^ 64 := by decide) :
    (cExamplesCode.rebase b H).fetch ((cExamplesCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) = some inst :=
  Program.fetch_fnAddr_add hfn (cExamplesCode_fetch_rebase_text h htext hoff)

theorem cExamplesCode_fetch_fnAddr_entry {b : BitVec 64} {H : String → Option (State → State)}
    {name : String} {off : Nat} {inst : Instr}
    (hfn : cExamplesCode.fnOff name = off) (htext : off + 0 < 44)
    (h : cExamplesCode_tree.fetchDecodeAt (off + 0) = some inst)
    (hoff : off + 0 < 2 ^ 64 := by decide) :
    (cExamplesCode.rebase b H).fetch ((cExamplesCode.rebase b H).fnAddr name) = some inst :=
  Program.fetch_fnAddr_entry hfn (cExamplesCode_fetch_rebase_text h htext hoff)

@[simp, arm64_norm] theorem cExamplesCode_fnOff_0x0 : cExamplesCode.fnOff "c_arith_shift" = 0 := rfl
@[simp, arm64_norm] theorem cExamplesCode_fnOff_0xc : cExamplesCode.fnOff "c_max_u64" = 12 := rfl
@[simp, arm64_norm] theorem cExamplesCode_fnOff_0x18 : cExamplesCode.fnOff "c_swap_u64" = 24 := rfl

abbrev cExamplesCode_frame (name : String) (sp : BitVec 64) : SepProp :=
  stackFrameFor cExamplesImage name sp

@[simp, arm64_norm, wp_norm] theorem cExamplesCode_fnSize_0x0 : Obj.fnSize cExamplesImage "c_arith_shift" = 12 := rfl
@[simp, arm64_norm, wp_norm] theorem cExamplesCode_fnSize_0xc : Obj.fnSize cExamplesImage "c_max_u64" = 12 := rfl
@[simp, arm64_norm, wp_norm] theorem cExamplesCode_fnSize_0x18 : Obj.fnSize cExamplesImage "c_swap_u64" = 20 := rfl

@[simp, arm64_norm, wp_norm] theorem cExamplesCode_frameBytes_0x0 : fnFrameBytes cExamplesImage "c_arith_shift" = 0 := rfl
@[simp, arm64_norm, wp_norm] theorem cExamplesCode_frameBytes_0xc : fnFrameBytes cExamplesImage "c_max_u64" = 0 := rfl
@[simp, arm64_norm, wp_norm] theorem cExamplesCode_frameBytes_0x18 : fnFrameBytes cExamplesImage "c_swap_u64" = 0 := rfl

@[simp, arm64_norm, wp_norm] theorem cExamplesObj_frameBytes_0x0 : fnFrameBytes cExamplesObj "c_arith_shift" = 0 := rfl
@[simp, arm64_norm, wp_norm] theorem cExamplesObj_frameBytes_0xc : fnFrameBytes cExamplesObj "c_max_u64" = 0 := rfl
@[simp, arm64_norm, wp_norm] theorem cExamplesObj_frameBytes_0x18 : fnFrameBytes cExamplesObj "c_swap_u64" = 0 := rfl

gen_fetches cExamplesCode cExamplesBin true [0x0 → 0x28]

register_fn_entry "c_arith_shift" Testing.CExamplesFixture.cExamplesCode Testing.CExamplesFixture.cExamplesBin Testing.CExamplesFixture.cExamplesCode_fnOff_0x0 0 12 0
register_fn_entry "c_max_u64" Testing.CExamplesFixture.cExamplesCode Testing.CExamplesFixture.cExamplesBin Testing.CExamplesFixture.cExamplesCode_fnOff_0xc 12 12 0
register_fn_entry "c_swap_u64" Testing.CExamplesFixture.cExamplesCode Testing.CExamplesFixture.cExamplesBin Testing.CExamplesFixture.cExamplesCode_fnOff_0x18 24 20 0

/-- `uint64_t c_arith_shift(uint64_t x) { return (x + 42u) * 3u; }` -/
c_spec cArithShiftSpec (x : u64) : u64
  returns 3#64 * (x + 42#64)

/-- `uint64_t c_max_u64(uint64_t a, uint64_t b) { return a > b ? a : b; }` -/
c_spec cMaxU64Spec (a : u64) (b : u64) : u64
  returns if BitVec.ult b a then a else b

/-- `void c_swap_u64(uint64_t *a, uint64_t *b)` -/
c_spec cSwapU64Spec (pa : ptr) (pb : ptr) (ghost va : u64) (ghost vb : u64)
  requires (pa ↦₆₄ va) ∗ (pb ↦₆₄ vb)
  ensures  (pa ↦₆₄ vb) ∗ (pb ↦₆₄ va)

/-- Self-contained 32-byte-prologue placed library fixture (`sub sp, sp, #32; stp x29, x30, [sp, #16];
    cbz x0, +12; add x0, x0, #1; b +8; mov x0, #1; ldp x29, x30, [sp, #16]; add sp, sp, #32; ret`). -/
def frame32Lib : Obj.PlacedLib :=
  { name := "frame32_fixture"
    text :=
      { code :=
          [0xff#8, 0x83#8, 0x00#8, 0xd1#8,
           0xfd#8, 0x7b#8, 0x01#8, 0xa9#8,
           0x60#8, 0x00#8, 0x00#8, 0xb4#8,
           0x00#8, 0x04#8, 0x00#8, 0x91#8,
           0x02#8, 0x00#8, 0x00#8, 0x14#8,
           0x20#8, 0x00#8, 0x80#8, 0xd2#8,
           0xfd#8, 0x7b#8, 0x41#8, 0xa9#8,
           0xff#8, 0x83#8, 0x00#8, 0x91#8,
           0xc0#8, 0x03#8, 0x5f#8, 0xd6#8]
        align := 4
        symbols := [("frame32_branch", 0x0)]
        relocs := []
        externs := [] }
    exports := ["frame32_branch"] }

def frame32TextProg : Program :=
  { code := frame32Lib.text.code, symbols := frame32Lib.text.symbols }

def frame32Text_tree : WordTree := word_tree_of% frame32TextProg

theorem frame32Text_code_eq : frame32Lib.text.code = frame32Text_tree.toBytes := by rfl_kernel

theorem frame32Text_tree_size : frame32Text_tree.checkSize? = some 9 := by rfl_kernel

def frame32Text_symChars : List (List Char × Nat) := sym_chars_of% frame32TextProg

theorem frame32Text_symbols_eq :
    frame32Lib.text.symbols = toStringSymbols frame32Text_symChars := by rfl_kernel

theorem frame32Text_symbols_fresh : allFreshCharSymbols frame32Text_symChars = true := by rfl_kernel

class Frame32Placement where
  pl : Obj.Placement
  placeable : frame32Lib.Placeable pl

def frame32Code [Frame32Placement] : Program := frame32Lib.program Frame32Placement.pl

gen_placed_fetches frame32Code frame32Lib frame32Text_tree frame32Text_code_eq
  frame32Text_tree_size via_placement Frame32Placement.pl Frame32Placement.placeable
  [0x0 → 0x20]
gen_placed_fnOffs frame32Code frame32Lib frame32Text_symChars frame32Text_symbols_eq
  frame32Text_symbols_fresh

end Testing.CExamplesFixture
