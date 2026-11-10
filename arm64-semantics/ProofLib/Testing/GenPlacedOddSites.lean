/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.GenPlacedOddSites

/-!
# Regression Tests for `gen_placed_odd_sites`

Tests `gen_placed_odd_sites` on the placed fixture `widgetLib` (`WidgetPlacement`):

| off | word | relocation |
|---|---|---|
| `0x0` | `NOP` | |
| `0x4` | `ADRP X1, tab+8` | `adrpHi21 tab 8` |
| `0x8` | `LDR X0, [X1, :lo12:tab+8]` | `ldst64Lo12 tab 8` |
| `0xc` | `LDRB W2, [X1, :lo12:tab+8]` | `ldst8Lo12 tab 8` |
| `0x10` | `STR W3, [X1, :lo12:tab+8]` | `ldst32Lo12 tab 8` |
| `0x14` | `LDRSW X4, [X1, :lo12:tab+8]` | `ldst32Lo12 tab 8` |
| `0x18` | `ADRP X5, blk` | `adrpHi21 blk 0` (block symbol at `0x34`) |
| `0x1c` | `LDR X5, [X5, :lo12:blk]` | `ldst64Lo12 blk 0` |
| `0x20` | `NOP` | |
| `0x24` | `LDR D0, [X1, :lo12:tab+8]` | `ldst64Lo12 tab 8` (SIMD) |
| `0x28` | `ADRP X6, tab-8` | `adrpHi21 tab (-8)` |
| `0x2c` | `ADRP X7, tbl` | `adrpHi21 tbl 0` |
| `0x30` | `ADD X7, X7, :lo12:tbl` | `addLo12 tbl 0` |
| `0x34` | `RET` (`blk`) | |

Exercises positive generation of plain `ADRP` pair-step hooks and `:lo12:` GPR load/store fetch
lemmas (external and block-local targets), end-to-end `wp_step` composition, idempotent re-runs,
and negative diagnostics on SIMD, negative-addend, relaxable-pair, and out-of-bounds sites.
-/

@[expose] public section

namespace Examples.Testing.GenPlacedOddSites

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

set_option linter.literalFetch false

def widgetBlk : CodeBlock where
  code := bytesOfWordLE 0xd503201f#32 ++ bytesOfWordLE 0x90000001#32 ++
    bytesOfWordLE 0xf9400020#32 ++ bytesOfWordLE 0x39400022#32 ++
    bytesOfWordLE 0xb9000023#32 ++ bytesOfWordLE 0xb9800024#32 ++
    bytesOfWordLE 0x90000005#32 ++ bytesOfWordLE 0xf94000a5#32 ++
    bytesOfWordLE 0xd503201f#32 ++ bytesOfWordLE 0xfd400020#32 ++
    bytesOfWordLE 0x90000006#32 ++ bytesOfWordLE 0x90000007#32 ++
    bytesOfWordLE 0x910000e7#32 ++ bytesOfWordLE 0xd65f03c0#32
  symbols := [("widget", 0), ("blk", 0x34)]
  relocs := [{ off := 0x4, kind := .adrpHi21, sym := "tab", addend := 8 },
             { off := 0x8, kind := .ldst64Lo12, sym := "tab", addend := 8 },
             { off := 0xc, kind := .ldst8Lo12, sym := "tab", addend := 8 },
             { off := 0x10, kind := .ldst32Lo12, sym := "tab", addend := 8 },
             { off := 0x14, kind := .ldst32Lo12, sym := "tab", addend := 8 },
             { off := 0x18, kind := .adrpHi21, sym := "blk" },
             { off := 0x1c, kind := .ldst64Lo12, sym := "blk" },
             { off := 0x24, kind := .ldst64Lo12, sym := "tab", addend := 8 },
             { off := 0x28, kind := .adrpHi21, sym := "tab", addend := -8 },
             { off := 0x2c, kind := .adrpHi21, sym := "tbl" },
             { off := 0x30, kind := .addLo12, sym := "tbl" }]

def widgetLib : PlacedLib where
  name := "widget"
  text := widgetBlk
  exports := ["widget"]

/-- A fixed placeable placement (the `via_placement` parameter). -/
class WidgetPlacement where
  pl : Placement
  placeable : widgetLib.Placeable pl

/-- The library placed at `WidgetPlacement.pl`. -/
def widgetPC [WidgetPlacement] : Program := widgetLib.program WidgetPlacement.pl

def widgetTextProg : Program := { code := widgetBlk.code }

def widgetTree : WordTree := word_tree_of% widgetTextProg

theorem widget_code_eq : widgetLib.text.code = widgetTree.toBytes := by rfl_kernel

theorem widget_tree_size : widgetTree.checkSize? = some 14 := by rfl_kernel

/-! ## Negative tests: skipped sites -/

/--
info: gen_placed_odd_sites: skipping load/store site 36: unsupported word 4248829984
---
info: gen_placed_odd_sites: skipping ADRP site 40: unsupported target tab + -8
-/
#guard_msgs in
gen_placed_odd_sites widgetPC widgetLib widgetTree widget_code_eq widget_tree_size
  via_placement WidgetPlacement.pl WidgetPlacement.placeable [0x0 → 0x34]

/-- error: Unknown identifier `widgetPC_pairStep_0x2c` -/
#guard_msgs (substring := true) in
example := @widgetPC_pairStep_0x2c

/-- error: Unknown identifier `widgetPC_rebase_fetch_0x24` -/
#guard_msgs (substring := true) in
example := @widgetPC_rebase_fetch_0x24

/-- error: Unknown identifier `widgetPC_pairStep_0x28` -/
#guard_msgs (substring := true) in
example := @widgetPC_pairStep_0x28

/-- error: gen_placed_odd_sites: offset 56 is out of bounds -/
#guard_msgs (substring := true) in
gen_placed_odd_sites widgetPC widgetLib widgetTree widget_code_eq widget_tree_size
  via_placement WidgetPlacement.pl WidgetPlacement.placeable [0x38]

-- A second run adds nothing: the existing lemmas are skipped silently, so only the two
-- unsupported sites report again.
/--
info: gen_placed_odd_sites: skipping load/store site 36: unsupported word 4248829984
---
info: gen_placed_odd_sites: skipping ADRP site 40: unsupported target tab + -8
-/
#guard_msgs in
gen_placed_odd_sites widgetPC widgetLib widgetTree widget_code_eq widget_tree_size
  via_placement WidgetPlacement.pl WidgetPlacement.placeable [0x0 → 0x34]

/-! ## Positive tests: the generated lemmas -/

-- The unrelocated words and the relaxable pair come from `gen_placed_fetches`.
gen_placed_fetches widgetPC widgetLib widgetTree widget_code_eq widget_tree_size
  via_placement WidgetPlacement.pl WidgetPlacement.placeable [0x0 → 0x34]

section
variable [WidgetPlacement]

example (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetPC.rebase b X).fetch (b + 0x8#64) = some (.ldr .W64 .X64 false (.gpr 0#5)
      (.Offset (.gpr 1#5) (lo12Of (WidgetPlacement.pl.ρ "tab" + 8#64)))) :=
  widgetPC_rebase_fetch_0x8 b X

example (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetPC.rebase b X).fetch (b + 0xc#64) = some (.ldr .W32 .B8 false (.gpr 2#5)
      (.Offset (.gpr 1#5) (lo12Of (WidgetPlacement.pl.ρ "tab" + 8#64)))) :=
  widgetPC_rebase_fetch_0xc b X

example (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetPC.rebase b X).fetch (b + 0x10#64) = some (.str .W32 (.gpr 3#5)
      (.Offset (.gpr 1#5) (lo12Of (WidgetPlacement.pl.ρ "tab" + 8#64)))) :=
  widgetPC_rebase_fetch_0x10 b X

example (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetPC.rebase b X).fetch (b + 0x14#64) = some (.ldr .W64 .W32 true (.gpr 4#5)
      (.Offset (.gpr 1#5) (lo12Of (WidgetPlacement.pl.ρ "tab" + 8#64)))) :=
  widgetPC_rebase_fetch_0x14 b X

/-- The block-symbol load/store target is written `pl.base + symOff`. -/
example (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetPC.rebase b X).fetch (b + 0x1c#64) = some (.ldr .W64 .X64 false (.gpr 5#5)
      (.Offset (.gpr 5#5) (lo12Of (WidgetPlacement.pl.base + 0x34#64)))) :=
  widgetPC_rebase_fetch_0x1c b X

/-- The plain `ADRP` lemma writes `pageOf T` into `X1` and steps one word. -/
example (b : BitVec 64) (X : String → Option (State → State)) {tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : b = WidgetPlacement.pl.base) (hpc : s.pc = b + 0x4#64) (hrun : s.status = .Running)
    (hnext : SepWP (widgetPC.rebase b X) tgt
      ((s.writeReg64 (.gpr 1#5) (pageOf (WidgetPlacement.pl.ρ "tab" + 8#64))).setPC
        (b + 0x8#64)) P post oom) :
    SepWP (widgetPC.rebase b X) tgt s P post oom :=
  widgetPC_pairStep_0x4 b X hb hpc hrun hnext

/-- A block-symbol `ADRP` target is written `b + symOff`. -/
example (b : BitVec 64) (X : String → Option (State → State)) {tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : b = WidgetPlacement.pl.base) (hpc : s.pc = b + 0x18#64) (hrun : s.status = .Running)
    (hnext : SepWP (widgetPC.rebase b X) tgt
      ((s.writeReg64 (.gpr 5#5) (pageOf (b + 0x34#64))).setPC (b + 0x1c#64)) P post oom) :
    SepWP (widgetPC.rebase b X) tgt s P post oom :=
  widgetPC_pairStep_0x18 b X hb hpc hrun hnext

/-- End-to-end check: `adrp x1, tab+8; ldr x0, [x1, :lo12:tab+8]` loads the doubleword at
    `T = pl.ρ "tab" + 8`, with `wp_step` applying the pair-step hook and the generated fetch lemma. -/
theorem adrp_ldr {s : State} {v : BitVec 64}
    (hpc : s.pc = WidgetPlacement.pl.base + 0x4#64) (hrun : s.status = .Running) :
    SepWP (widgetPC.rebase WidgetPlacement.pl.base (fun _ => none))
      (WidgetPlacement.pl.base + 0xc#64) s
      ((WidgetPlacement.pl.ρ "tab" + 8#64) ↦₆₄ v)
      (fun sf _ => sf.readReg64 .x0 = v ∧
        sf.readReg64 .x1 = pageOf (WidgetPlacement.pl.ρ "tab" + 8#64)) := by
  wp_step
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm]

end

/-- info: 'Examples.Testing.GenPlacedOddSites.adrp_ldr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms adrp_ldr

/--
info: 'Examples.Testing.GenPlacedOddSites.widgetPC_rebase_fetch_0x1c' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms widgetPC_rebase_fetch_0x1c

end Examples.Testing.GenPlacedOddSites
