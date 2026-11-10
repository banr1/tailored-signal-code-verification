/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Placed
public import ProofLib.GenPlacedFetches
public meta import ProofLib.Process
public meta import ProofLib.ProgramReflection

/-!
# Multi-Block Placed Library Tests

Tests `MultiPlacedLib` layout-generic `subroutineOk` proofs, cross-block calls (`wp_call_block`),
linker relaxation (`NOP`+`ADR`), ELF placement verification (`checkInElf`, `checkPlaceable`),
shared external hooks, indexed symbol lookup (`gen_multi_sym_index`), and sorted-range block
disjointness.
-/

@[expose] public section

namespace Examples.Testing.PlacedMultiTest

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
  ProofLib.ObjectLoad

set_option maxRecDepth 200000

/-- Little-endian bytes of a list of 32-bit instruction words. -/
def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-! ## Layout-generic `MultiPlacedLib.subroutineOk` and cross-block proof transfer -/

section ProofTransfer

set_option linter.literalFetch false

/-- Two-block synthetic library `multiWidgetLib`:
    - Block 0 (`caller`, 24 B):
      `0x0: adrp x0, tab; 0x4: add x0, x0, :lo12:tab; 0x8: mov x9, x30; 0xc: bl callee; 0x10: mov x30, x9; 0x14: ret`
      (with `externs := ["callee"]` so `BL callee` is a cross-block branch).
    - Block 1 (`callee`, 8 B):
      `0x0: ldr x0, [x0]; 0x4: ret`
    - Data: `tab` (8 B, read-only). -/
def widgetBlk0 : CodeBlock where
  code := wordsLE [
    0x90000000#32, 0x91000000#32, 0xaa1e03e9#32,
    0x94000000#32, 0xaa0903fe#32, 0xd65f03c0#32]
  align := 4
  symbols := [("caller", 0)]
  relocs := [
    { off := 0, kind := .adrpHi21, sym := "tab" },
    { off := 4, kind := .addLo12, sym := "tab" },
    { off := 12, kind := .call26, sym := "callee" }]
  externs := ["callee"]

def widgetBlk1 : CodeBlock where
  code := wordsLE [0xf9400000#32, 0xd65f03c0#32]
  align := 4
  symbols := [("callee", 0)]
  relocs := []

def multiWidgetLib : MultiPlacedLib where
  name := "multi_widget"
  blocks := [widgetBlk0, widgetBlk1]
  data := [{ sym := "tab", align := 8, readOnly := true, bytes := List.replicate 8 0#8 }]
  exports := ["caller", "callee"]

def widgetLib0 : PlacedLib := multiWidgetLib.blockLib 0
def widgetLib1 : PlacedLib := multiWidgetLib.blockLib 1

class WidgetMultiPlacement where
  mpl : MultiPlacement
  placeable : multiWidgetLib.Placeable mpl

def widgetPl0 [WidgetMultiPlacement] : Placement :=
  multiWidgetLib.blockPlacement WidgetMultiPlacement.mpl 0

theorem widgetPlaceable0 [WidgetMultiPlacement] : widgetLib0.Placeable widgetPl0 :=
  multiWidgetLib.placeable_blockLib (by decide) WidgetMultiPlacement.placeable

def widgetPl1 [WidgetMultiPlacement] : Placement :=
  multiWidgetLib.blockPlacement WidgetMultiPlacement.mpl 1

theorem widgetPlaceable1 [WidgetMultiPlacement] : widgetLib1.Placeable widgetPl1 :=
  multiWidgetLib.placeable_blockLib (by decide) WidgetMultiPlacement.placeable

def widgetPC0 [WidgetMultiPlacement] : Program := widgetLib0.program widgetPl0
def widgetPC1 [WidgetMultiPlacement] : Program := widgetLib1.program widgetPl1

def widgetProg0 : Program := { code := widgetBlk0.code, symbols := widgetBlk0.symbols }
def widgetProg1 : Program := { code := widgetBlk1.code, symbols := widgetBlk1.symbols }

def widgetTree0 : WordTree := word_tree_of% widgetProg0
def widgetTree1 : WordTree := word_tree_of% widgetProg1

theorem widget0_code_eq : widgetLib0.text.code = widgetTree0.toBytes := by rfl_kernel
theorem widget0_tree_size : widgetTree0.checkSize? = some 6 := by rfl_kernel

theorem widget1_code_eq : widgetLib1.text.code = widgetTree1.toBytes := by rfl_kernel
theorem widget1_tree_size : widgetTree1.checkSize? = some 2 := by rfl_kernel

def widgetSymChars0 : List (List Char × Nat) := sym_chars_of% widgetProg0
theorem widget0_symbols_eq : widgetLib0.text.symbols = toStringSymbols widgetSymChars0 := by
  rfl_kernel
theorem widget0_symbols_fresh : allFreshCharSymbols widgetSymChars0 = true := by rfl_kernel

def widgetSymChars1 : List (List Char × Nat) := sym_chars_of% widgetProg1
theorem widget1_symbols_eq : widgetLib1.text.symbols = toStringSymbols widgetSymChars1 := by
  rfl_kernel
theorem widget1_symbols_fresh : allFreshCharSymbols widgetSymChars1 = true := by rfl_kernel

gen_placed_fetches widgetPC0 widgetLib0 widgetTree0 widget0_code_eq widget0_tree_size
  via_placement widgetPl0 widgetPlaceable0 [0x0 → 0x14]
gen_placed_fnOffs widgetPC0 widgetLib0 widgetSymChars0 widget0_symbols_eq widget0_symbols_fresh

gen_placed_fetches widgetPC1 widgetLib1 widgetTree1 widget1_code_eq widget1_tree_size
  via_placement widgetPl1 widgetPlaceable1 [0x0 → 0x4]
gen_placed_fnOffs widgetPC1 widgetLib1 widgetSymChars1 widget1_symbols_eq widget1_symbols_fresh

abbrev wMpl [WidgetMultiPlacement] : MultiPlacement := WidgetMultiPlacement.mpl

/-- Specification of `callee`: reads `x0 ↦₆₄ v`, returns `v` in `x0`, and preserves `x9`. -/
def calleeSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (ptr, v) s0 => ⌜s0.readReg64 .x0 = ptr⌝ ∗ (ptr ↦₆₄ v)
  post := fun (ptr, v) s0 sf =>
    ⌜sf.readReg64 .x0 = v ∧ sf.readReg64 .x9 = s0.readReg64 .x9⌝ ∗ (ptr ↦₆₄ v)

theorem callee_ok [WidgetMultiPlacement] :
    subroutine_ok (widgetPC1.rebase widgetPl1.base (fun _ => none))
      widgetPl1.base (multiWidgetLib.withCodeLoaded wMpl calleeSpec) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, calleeSpec]
  wp_entry "callee" pv s0
  wp_steps
  wp_done

/-- Layout-generic proof of `callee` (block 1) for any `mpl` with `multiWidgetLib.Placeable mpl`. -/
theorem callee_subroutineOk :
    multiWidgetLib.subroutineOk "callee" (fun _ => calleeSpec) :=
  ⟨by decide, 1, 0, rfl, fun mpl hpl => by
    have hfn : multiWidgetLib.fnAddr mpl "callee" = mpl.base 1 := by
      simp [MultiPlacedLib.fnAddr, lookupBlockSym, lookupBlockSymAux, lookup,
        multiWidgetLib, widgetBlk0, widgetBlk1]
    rw [hfn]
    exact @callee_ok ⟨mpl, hpl⟩⟩

/-- Specification of `caller` (block 0): loads `v` from `mpl.ρ "tab"` by relaxing or executing
    `adrp x0, tab; add x0, x0, :lo12:tab` and calling `callee` in block 1. -/
def callerSpec (mpl : MultiPlacement) : Spec (BitVec 64) where
  pre := fun v _ => (mpl.ρ "tab") ↦₆₄ v
  post := fun v _ sf => ⌜sf.readReg64 .x0 = v⌝ ∗ ((mpl.ρ "tab") ↦₆₄ v)

theorem caller_ok [WidgetMultiPlacement] :
    subroutine_ok (widgetPC0.rebase widgetPl0.base (fun _ => none))
      widgetPl0.base (multiWidgetLib.withCodeLoaded wMpl (callerSpec wMpl)) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, callerSpec]
  wp_entry "caller" v s0
  have hpc0 : s0.pc = widgetPl0.base + 0#64 := by simp [hpc]
  wp_steps
  wp_call_block callee_ok (wMpl.ρ "tab", v)
  wp_steps
  wp_done

/-- Layout-generic proof of `caller` (block 0) calling `callee` (block 1), valid under both
    unrelaxed (`ADRP`+`ADD`) and linker-relaxed (`NOP`+`ADR`) placements. -/
theorem caller_subroutineOk :
    multiWidgetLib.subroutineOk "caller" callerSpec :=
  ⟨by decide, 0, 0, rfl, fun mpl hpl => by
    have hfn : multiWidgetLib.fnAddr mpl "caller" = mpl.base 0 := by
      simp [MultiPlacedLib.fnAddr, lookupBlockSym, lookupBlockSymAux, lookup,
        multiWidgetLib, widgetBlk0, widgetBlk1]
    rw [hfn]
    exact @caller_ok ⟨mpl, hpl⟩⟩

/-- Concrete ELF containing `multiWidgetLib` with block 0 relaxed (`NOP`+`ADR`) and block 1
    placed non-contiguously at `0x402000`. -/
def widgetElf : ElfImage where
  entry := 0x400000#64
  phdrVaddr := 0x400040#64
  phnum := 3
  segments := [
    { start := 0x400000#64, perm := Perm.rx,
      bytes := wordsLE [
        0xd503201f#32, 0x10017fe0#32, 0xaa1e03e9#32,
        0x940007fd#32, 0xaa0903fe#32, 0xd65f03c0#32] },
    { start := 0x402000#64, perm := Perm.rx,
      bytes := wordsLE [0xf9400000#32, 0xd65f03c0#32] },
    { start := 0x403000#64, perm := Perm.ro, bytes := List.replicate 8 0#8 }]
  brkStart := 0x404000#64
  symbols := [("caller", 0x400000#64), ("callee", 0x402000#64)]

def widgetMpl : MultiPlacement where
  base := fun i => if i == 0 then 0x400000#64 else 0x402000#64
  ρ := fun s => if s == "tab" then 0x403000#64 else 0#64
  relax := fun i off => i == 0 && off == 0

theorem widget_in_elf :
    multiWidgetLib.Placeable widgetMpl ∧ multiWidgetLib.InElf widgetElf widgetMpl :=
  multiWidgetLib.checkInElf_spec (by decide +kernel)

/-- End-to-end transfer of `caller_subroutineOk` into `Steps Program.pureMem` over `widgetElf`,
    discharging `multiWidgetLib.CodeLoaded` automatically from `widget_in_elf`. -/
theorem caller_ok_in_widgetElf {inputs : ProcessInputs} {s_init s0 : State}
    (hload : widgetElf.loadState inputs = .ok s_init)
    (hfrozen : s_init.mem.KeepsFrozen s0.mem)
    (hpc : s0.pc = multiWidgetLib.fnAddr widgetMpl "caller")
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    {v : BitVec 64} {R : SepProp}
    (hpre : s0.mem ⊨ ((widgetMpl.ρ "tab") ↦₆₄ v) ∗ R) :
    ∃ sf : State,
      Steps Program.pureMem s0 sf ∧ Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ (⌜sf.readReg64 .x0 = v⌝ ∗ ((widgetMpl.ρ "tab") ↦₆₄ v)) ∗ R) :=
  multiWidgetLib.subroutineOk_toPureMem caller_subroutineOk widget_in_elf.1 widget_in_elf.2
    hload (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    hfrozen hpc hrun hsp (i := 0) (off := 0) rfl hpre
    (fun pc _ _ h => by simp at h)

end ProofTransfer

/-! ## Negative `#guard_msgs` tests for `MultiPlacedLib.checkInElf` -/

/-- Flipping a code byte in block 1 (`callee`) is rejected by `checkInElf`. -/
def widgetElfBadByte : ElfImage :=
  { widgetElf with
    segments := [
      { start := 0x400000#64, perm := Perm.rx,
        bytes := wordsLE [
          0xd503201f#32, 0x10017fe0#32, 0xaa1e03e9#32,
          0x940007fd#32, 0xaa0903fe#32, 0xd65f03c0#32] },
      { start := 0x402000#64, perm := Perm.rx,
        bytes := wordsLE [0xf9400001#32, 0xd65f03c0#32] },
      { start := 0x403000#64, perm := Perm.ro, bytes := List.replicate 8 0#8 }] }

/-- Overlapping block 0 (`[0x400000, 0x400010)`) and block 1 (`[0x400008, 0x400010)`). -/
def widgetMplOverlap : MultiPlacement :=
  { widgetMpl with base := fun i => if i == 0 then 0x400000#64 else 0x400008#64 }

/-- Unrelaxed `relax := false` placement checked against the relaxed (`NOP`+`ADR`) `widgetElf`. -/
def widgetMplUnrelaxed : MultiPlacement :=
  { widgetMpl with relax := fun _ _ => false }

/-- Wrong `.symtab` address for exported symbol `"callee"`. -/
def widgetElfBadSym : ElfImage :=
  { widgetElf with symbols := [("caller", 0x400000#64), ("callee", 0x402004#64)] }

/--
error: Tactic `decide` proved that the proposition
  multiWidgetLib.checkInElf widgetMpl widgetElfBadByte = true
is false
-/
#guard_msgs (error, drop info) in
example : multiWidgetLib.checkInElf widgetMpl widgetElfBadByte = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  multiWidgetLib.checkPlaceable widgetMplOverlap = true
is false
-/
#guard_msgs (error, drop info) in
example : multiWidgetLib.checkPlaceable widgetMplOverlap = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  multiWidgetLib.checkInElf widgetMplUnrelaxed widgetElf = true
is false
-/
#guard_msgs (error, drop info) in
example : multiWidgetLib.checkInElf widgetMplUnrelaxed widgetElf = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  multiWidgetLib.checkInElf widgetMpl widgetElfBadSym = true
is false
-/
#guard_msgs (error, drop info) in
example : multiWidgetLib.checkInElf widgetMpl widgetElfBadSym = true := by decide +kernel

/--
error: wp_call_block: expected `subroutine_ok` contract, got `True`
-/
#guard_msgs (error, drop info) in
example : True := by
  have h : True := trivial
  wp_call_block h

/-! ## Shared external hooks and order-independent `dataEntriesDisjointB` -/

/-- Two blocks sharing the same `externs` list can switch programs under an arbitrary hook map `X`. -/
def hookedWidgetLib : MultiPlacedLib where
  name := "hooked_widget"
  blocks := [
    { code := wordsLE [0x94000000#32, 0xd65f03c0#32]
      symbols := [("caller", 0)]
      relocs := [{ off := 0, kind := .call26, sym := "ext_alloc" }]
      externs := ["ext_alloc"] },
    { code := wordsLE [0xd65f03c0#32]
      symbols := [("callee", 0)]
      externs := ["ext_alloc"] }]
  exports := ["caller", "callee"]

example (mpl : MultiPlacement) (X : String → Option (State → State))
    {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : hookedWidgetLib.CodeLoaded mpl s.mem)
    (h : SepWP (hookedWidgetLib.blockProgram mpl 1 X) target_pc s Pre post oom) :
    SepWP (hookedWidgetLib.blockProgram mpl 0 X) target_pc s Pre post oom :=
  hookedWidgetLib.sepWP_of_other_block_hooks (j := 1) (by decide) rfl hcl h

/-- Positive: read-only entries may overlap (tail-merged strings) and entries may appear in
    non-ascending address order as long as writable entries are pairwise disjoint. -/
example : Obj.Interned.dataEntriesDisjointB
    [(true, 0x2002#64, 1), (true, 0x2000#64, 3), (false, 0x1000#64, 8)] = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  Interned.dataEntriesDisjointB [(false, 4096#64, 8), (true, 4100#64, 4)] = true
is false
-/
#guard_msgs (error, drop info) in
/-- Negative: a writable entry overlapping a read-only entry is rejected. -/
example : Obj.Interned.dataEntriesDisjointB
    [(false, 0x1000#64, 8), (true, 0x1004#64, 4)] = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  Interned.dataEntriesDisjointB [(true, 18446744073709551612#64, 8)] = true
is false
-/
#guard_msgs (error, drop info) in
/-- Negative: an entry whose `[addr, addr + len)` wraps past `2 ^ 64` is rejected. -/
example : Obj.Interned.dataEntriesDisjointB
    [(true, 0xfffffffffffffffc#64, 8)] = true := by
  decide +kernel

/-! ## Indexed lookup (`SymIndex`, `gen_multi_sym_index`) and `SameSymbolLayout` -/

section IndexedMultiSym

gen_multi_sym_index widgetSymIdx multiWidgetLib

-- Positive: `SameSymbolLayout` transfers `lookupBlockSym`, `fnAddr`, `resolve`, and `target` across
-- a code-mutated variant without re-checking symbol indices:
def multiWidgetVariant : MultiPlacedLib :=
  { multiWidgetLib with
    blocks :=
      [ { widgetBlk0 with code := widgetBlk0.code ++ wordsLE [0xd503201f#32] }
      , { widgetBlk1 with code := wordsLE [0xd2800000#32, 0xd65f03c0#32] } ] }

theorem multiWidget_sameSymbolLayout :
    multiWidgetLib.SameSymbolLayout multiWidgetVariant := rfl

example (mpl : MultiPlacement) :
    multiWidgetVariant.fnAddr mpl "callee" = mpl.base 1 + 0#64 := by
  rw [← MultiPlacedLib.fnAddr_eq_of_sameSymbolLayout multiWidget_sameSymbolLayout]
  exact widgetSymIdx.fnAddr_eq_base mpl (by decide +kernel)

example (mpl : MultiPlacement) (r : RelocEntry) :
    widgetBlk0.target (multiWidgetVariant.blockPlacement mpl 0) r =
      widgetBlk0.target (multiWidgetLib.blockPlacement mpl 0) r :=
  CodeBlock.target_blockPlacement_eq_of_sameSymbolLayout
    multiWidget_sameSymbolLayout.symm widgetBlk0 mpl 0 r

-- Hash collision test: `"col_az"`, `"col_ib"`, `"col_qJ"` share the same `hashChars1024` bucket,
-- and `"dcol_az"`, `"dcol_ib"`, `"dcol_qJ"` share the same `hashChars1024` bucket:
def collisionMultiLib : MultiPlacedLib where
  name := "collision_multi"
  blocks :=
    [ { code := wordsLE [0xd65f03c0#32], symbols := [("col_az", 0)] }
    , { code := wordsLE [0xd503201f#32, 0xd65f03c0#32], symbols := [("col_ib", 4)] } ]
  data :=
    [ { sym := "dcol_az", readOnly := true, bytes := [1#8] }
    , { sym := "dcol_ib", readOnly := true, bytes := [2#8] } ]
  exports := ["col_az", "col_ib"]

gen_multi_sym_index collisionMultiIdx collisionMultiLib

example : hashChars1024 "col_az".toList = hashChars1024 "col_ib".toList ∧
    hashChars1024 "col_ib".toList = hashChars1024 "col_qJ".toList ∧
    hashChars1024 "dcol_az".toList = hashChars1024 "dcol_ib".toList ∧
    hashChars1024 "dcol_ib".toList = hashChars1024 "dcol_qJ".toList := by decide +kernel

example : collisionMultiIdx.lookupBlockSym "col_az" = some (0, 0) := by decide +kernel
example : collisionMultiIdx.lookupBlockSym "col_ib" = some (1, 4) := by decide +kernel
example : collisionMultiIdx.lookupBlockSym "col_qJ" = none := by decide +kernel
example : collisionMultiIdx.notBlockSym "col_qJ" = true := by decide +kernel
example : (collisionMultiIdx.findDataSym "dcol_az").map (·.1) = some 0 := by decide +kernel
example : (collisionMultiIdx.findDataSym "dcol_ib").map (·.1) = some 1 := by decide +kernel
example : collisionMultiIdx.findDataSym "dcol_qJ" = none := by decide +kernel

-- Negative `#guard_msgs`: duplicate symbol across two blocks is rejected at elaboration time:
def dupBlockSymLib : MultiPlacedLib where
  name := "dup_block"
  blocks :=
    [ { code := wordsLE [0xd65f03c0#32], symbols := [("shared_sym", 0)] }
    , { code := wordsLE [0xd65f03c0#32], symbols := [("shared_sym", 0)] } ]

/--
error: gen_multi_sym_index: duplicate symbol "shared_sym" across `dupBlockSymLib.blocks` (blocks 0 and 1)
-/
#guard_msgs in
gen_multi_sym_index dupBlockIdx dupBlockSymLib

-- Negative `#guard_msgs`: duplicate `.data` symbol is rejected at elaboration time:
def dupDataSymLib : MultiPlacedLib where
  name := "dup_data"
  blocks := [{ code := wordsLE [0xd65f03c0#32], symbols := [("f", 0)] }]
  data :=
    [ { sym := "ro_dup", readOnly := true, bytes := [0#8] }
    , { sym := "ro_dup", readOnly := true, bytes := [1#8] } ]

/--
error: gen_multi_sym_index: duplicate data symbol "ro_dup" in `dupDataSymLib.data` (indices 0 and 1)
-/
#guard_msgs in
gen_multi_sym_index dupDataIdx dupDataSymLib

end IndexedMultiSym

/-! ## Linear sorted-range block disjointness in `Interned.multiPlaceableB` -/

section SortedRanges

/-- Two one-instruction blocks (`RET`) used by the sorted / unsorted / overlapping layouts. -/
def sortedRangesL : Obj.Interned.MultiLib where
  name := "sorted_ranges"
  names := ["f", "g"]
  blocks :=
    [ { code := wordsLE [0xd65f03c0#32], symbols := [(0, 0)] }
    , { code := wordsLE [0xd65f03c0#32], symbols := [(1, 0)] } ]

def sortedRangesMly (b0 b1 : BitVec 64) : Obj.Interned.MultiLayout :=
  { bases := [b0, b1], addrs := [b0, b1] }

-- Positive: address-sorted blocks pass the linear walk and `multiPlaceableB`:
example : sortedRangesB (·.code.length) 0 (sortedRangesMly 0x400000#64 0x400004#64).bases
    sortedRangesL.blocks = true := by decide +kernel
example : Obj.Interned.multiPlaceableB sortedRangesL (sortedRangesMly 0x400000#64 0x400004#64)
    = true := by decide +kernel

-- Positive: disjoint blocks in decreasing address order fail the linear walk but are still
-- accepted by the pairwise fallback:
example : sortedRangesB (·.code.length) 0 (sortedRangesMly 0x400010#64 0x400000#64).bases
    sortedRangesL.blocks = false := by decide +kernel
example : Obj.Interned.multiPlaceableB sortedRangesL (sortedRangesMly 0x400010#64 0x400000#64)
    = true := by decide +kernel

-- Negative: fewer bases than blocks fails the linear walk:
example : sortedRangesB (·.code.length) 0 [0x400000#64] sortedRangesL.blocks = false := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  Interned.multiPlaceableB sortedRangesL (sortedRangesMly 4194304#64 4194304#64) = true
is false
-/
#guard_msgs (error, drop info) in
example : Obj.Interned.multiPlaceableB sortedRangesL (sortedRangesMly 0x400000#64 0x400000#64)
    = true := by decide +kernel

end SortedRanges

end Examples.Testing.PlacedMultiTest
