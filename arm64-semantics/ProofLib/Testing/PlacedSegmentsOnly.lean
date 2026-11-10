/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.SegmentsOnly
public import ProofLib.Testing.PlacedMulti

/-!
# Segment-Only Placement Transfer

Tests `MultiPlacedLib.codeLoaded_of_inElf_segments` on an `ElfImage` whose `.symtab` has been
stripped (`STB_LOCAL` exports), confirming `CodeLoaded` transfer from `PT_LOAD` segments alone and
checking that `.symtab` export lookup returns `none`.
-/

set_option autoImplicit false

@[expose] public section

namespace Examples.Testing.PlacedSegmentsOnly

open Arm64 Arm64.Obj Arm64.Process ProofLib
open Examples.Testing.PlacedMultiTest

/-- `widgetElf` with its `.symtab` dropped (the exports are local symbols). -/
def widgetElfLocal : ElfImage := { widgetElf with symbols := [] }

/-- `CodeLoaded` holds in every initial state of `widgetElfLocal`. -/
theorem widget_codeLoaded_local {inputs : ProcessInputs} {s : State}
    (hload : widgetElfLocal.loadState inputs = .ok s) :
    multiWidgetLib.CodeLoaded widgetMpl s.mem :=
  MultiPlacedLib.codeLoaded_of_inElf_segments (img := widgetElfLocal) widget_in_elf.1
    widget_in_elf.2 rfl hload

/-- `widgetElfLocal` has no `.symtab` entry for the export `caller`. -/
example : lookupUnique "caller" widgetElfLocal.symbols = none := by decide

/--
error: Tactic `rfl` failed: The left-hand side
  lookupUnique "caller" widgetElfLocal.symbols
is not definitionally equal to the right-hand side
  some 4194304#64

⊢ lookupUnique "caller" widgetElfLocal.symbols = some 4194304#64
-/
#guard_msgs in
example : lookupUnique "caller" widgetElfLocal.symbols = some 0x400000#64 := by rfl

end Examples.Testing.PlacedSegmentsOnly
