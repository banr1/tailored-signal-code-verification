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

/-!
# Tests for `gen_block_fetches`

Positive and negative elaboration tests for `gen_block_fetches` over the two-block fixture
`widgetMultiLib`, covering option combinations (`rebase`, `rho`, `sub`, `irreducible`), explicit
offset ranges, zero-padded block indices, and error diagnostics.
-/

@[expose] public section

namespace Examples.Testing.GenBlockFetches

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w =>
    [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

def widgetBlk0 : CodeBlock where
  code := wordsLE [0xaa0103e0#32, 0xd65f03c0#32]
  align := 4
  symbols := [("widget_entry", 0)]
  relocs := []

def widgetBlk1 : CodeBlock where
  code := wordsLE [0xf9400000#32, 0x91000400#32, 0xd65f03c0#32]
  align := 4
  symbols := [("widget_leaf", 0)]
  relocs := []

def widgetMultiLib : MultiPlacedLib where
  name := "widget_multi"
  blocks := [widgetBlk0, widgetBlk1]
  data := []
  exports := ["widget_entry", "widget_leaf"]

class WidgetPlacement where
  mpl : MultiPlacement
  placeable : widgetMultiLib.Placeable mpl

abbrev widgetMpl [WidgetPlacement] : MultiPlacement := WidgetPlacement.mpl

/-! ## Positive: every option, default range -/

gen_block_fetches widget 0 widgetMultiLib WidgetPlacement 2 rebase rho sub irreducible

example : widgetLib0 = widgetMultiLib.blockLib 0 := rfl
example : widgetTree0.checkSize? = some 2 := widget0_tree_size
example : widgetLib0.text.code = widgetTree0.toBytes := widget0_code_eq
example [WidgetPlacement] : widgetLib0.Placeable widgetPl0 := widgetPlaceable0
example [WidgetPlacement] : widgetPl0.base = widgetMpl.base 0 := widgetPl0_base
example [WidgetPlacement] (sym : String) : widgetMultiLib.resolve widgetMpl sym = widgetPl0.ρ sym :=
  widgetPl0_rho sym
example [WidgetPlacement] :
    (widgetMultiLib.blockProgram widgetMpl 0).rebase (widgetMpl.base 0) (fun _ => none) =
      widgetPC0.rebase widgetPl0.base (fun _ => none) := widgetPC0_rebase
example [WidgetPlacement] {e : BitVec 64} {spec : Spec Unit}
    (h : subroutine_ok (widgetMultiLib.blockProgram widgetMpl 0) e spec) :
    subroutine_ok (widgetPC0.rebase widgetPl0.base (fun _ => none)) e spec := widgetPC0_sub h

#guard_msgs (drop info) in
#check @widgetPC0_rebase_fetch_base
#guard_msgs (drop info) in
#check @widgetPC0_rebase_fetch_0x4

-- `irreducible`: `widgetPl0` no longer unfolds during elaboration.
/--
error: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  widgetPl0 = widgetMultiLib.blockPlacement widgetMpl 0
-/
#guard_msgs in
example [WidgetPlacement] : widgetPl0 = widgetMultiLib.blockPlacement widgetMpl 0 := rfl

/-! ## Positive: no options, padded numeral, explicit range -/

gen_block_fetches widget 01 widgetMultiLib WidgetPlacement 3 [0x4]

example : widgetLib01 = widgetMultiLib.blockLib 1 := rfl
example : widgetTree01.checkSize? = some 3 := widget01_tree_size
example [WidgetPlacement] : widgetPl01 = widgetMultiLib.blockPlacement widgetMpl 1 := rfl

#guard_msgs (drop info) in
#check @widgetPC01_rebase_fetch_0x4

/-! ## Negative -/

/-- error: Unknown identifier `widgetPC01_rebase_fetch_base` -/
#guard_msgs in
#check @widgetPC01_rebase_fetch_base

/-- error: Unknown identifier `widgetPC01_rebase_fetch_0x8` -/
#guard_msgs in
#check @widgetPC01_rebase_fetch_0x8

/-- error: Unknown identifier `widgetPC01_rebase` -/
#guard_msgs in
#check @widgetPC01_rebase

/-- error: Unknown identifier `widgetPl01_rho` -/
#guard_msgs in
#check @widgetPl01_rho

/-- error: Unknown identifier `widgetPC01_sub` -/
#guard_msgs in
#check @widgetPC01_sub

/-- error: gen_block_fetches: the word count must be positive -/
#guard_msgs in
gen_block_fetches widget 1 widgetMultiLib WidgetPlacement 0

/-- error: gen_block_fetches: the prefix must be an atomic identifier -/
#guard_msgs in
gen_block_fetches widget.w 1 widgetMultiLib WidgetPlacement 3

/-- error: gen_block_fetches: expected a decimal block index, got 0x1 -/
#guard_msgs in
gen_block_fetches widget 0x1 widgetMultiLib WidgetPlacement 3

/-- error: Unknown constant `gizmoMpl` -/
#guard_msgs in
gen_block_fetches gizmo 1 widgetMultiLib WidgetPlacement 3

end Examples.Testing.GenBlockFetches
