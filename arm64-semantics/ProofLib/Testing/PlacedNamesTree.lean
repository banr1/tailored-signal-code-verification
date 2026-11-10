/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.NamesTree

/-!
# Names-Tree Projection Tests for Interned Libraries

Tests `Lib.toLibT_eq`, `namesTreeOkChunks_cons`, and `namesTreeOkChunks_nil` on a five-name
interned library `Widget` (including out-of-range weak-reference resolution), together with
negative `#guard_msgs` checks for mismatched names and table lengths.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib.Testing.PlacedNamesTree

open Arm64 Arm64.Obj Arm64.Obj.Interned ProofLib.ProgramReflection ProofLib.Placed.Split

/-- Synthetic interned library with one symbol, two relocations, an extern, an out-of-range weak
    reference (index 7), one relocated data object, and one export. -/
def Widget : Lib where
  name := "widget"
  names := ["alpha", "beta", "gamma", "delta", "epsilon"]
  code := List.replicate 8 0#8
  symbols := [(0, 0)]
  relocs := [⟨0, .call26, 1, 0, false⟩, ⟨4, .adrpHi21, 3, 0, false⟩]
  externs := [1]
  weakRefs := [7]
  data := [{ sym := 3, align := 8, bytes := List.replicate 8 0#8,
             relocs := [⟨0, .abs64, 2, 0, false⟩] }]
  exports := [0]

def widgetTree : VecTree String :=
  .node 2 (.node 1 (.node 0 .leaf "alpha" .leaf) "beta" .leaf) "gamma"
    (.node 1 (.node 0 .leaf "delta" .leaf) "epsilon" .leaf)

def widgetPlaced : PlacedLib where
  name := "widget"
  text :=
    { code := List.replicate 8 0#8, symbols := [("alpha", 0)]
      relocs := [⟨0, .call26, "beta", 0, false⟩, ⟨4, .adrpHi21, "delta", 0, false⟩]
      externs := ["beta"], weakRefs := [""] }
  data := [{ sym := "delta", align := 8, bytes := List.replicate 8 0#8,
             relocs := [⟨0, .abs64, "gamma", 0, false⟩] }]
  exports := ["alpha"]

/-! ## Projection Equivalence -/

theorem len : rLen Widget.names = 5 := by rfl_kernel

theorem names0 : namesFrom widgetTree (3 - 0) 0 = rTake (3 - 0) (rDrop 0 Widget.names) := by
  rfl_kernel
theorem names1 : namesFrom widgetTree (5 - 3) 3 = rDrop 3 Widget.names := by rfl_kernel
theorem namesAll : namesFrom widgetTree (5 - 0) 0 = rDrop 0 Widget.names := by rfl_kernel

theorem widget_eq : Widget.toLibT 5 widgetTree = Widget.toLib :=
  Lib.toLibT_eq len (namesTreeOkChunks_cons names0 (namesTreeOkChunks_nil names1))

theorem widget_eq' : Widget.toLibT 5 widgetTree = Widget.toLib :=
  Lib.toLibT_eq (js := []) len (namesTreeOkChunks_nil namesAll)

theorem placed_eqT : widgetPlaced = Widget.toLibT 5 widgetTree := by rfl_kernel

theorem placed_eq : widgetPlaced = Widget.toLib := placed_eqT.trans widget_eq

/-! ## Negative Tests -/

def widgetTreeBad : VecTree String :=
  .node 2 (.node 1 (.node 0 .leaf "alpha" .leaf) "betta" .leaf) "gamma"
    (.node 1 (.node 0 .leaf "delta" .leaf) "epsilon" .leaf)

def widgetTreeShort : VecTree String :=
  .node 2 (.node 1 (.node 0 .leaf "alpha" .leaf) "beta" .leaf) "gamma"
    (.node 0 .leaf "delta" .leaf)

/--
error: Tactic `decide` proved that the proposition
  namesFrom widgetTreeBad (3 - 0) 0 = rTake (3 - 0) (rDrop 0 Widget.names)
is false
-/
#guard_msgs (error, drop info) in
example : namesFrom widgetTreeBad (3 - 0) 0 = rTake (3 - 0) (rDrop 0 Widget.names) := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  namesFrom widgetTreeShort (5 - 3) 3 = rDrop 3 Widget.names
is false
-/
#guard_msgs (error, drop info) in
example : namesFrom widgetTreeShort (5 - 3) 3 = rDrop 3 Widget.names := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  namesFrom widgetTree (4 - 3) 3 = rDrop 3 Widget.names
is false
-/
#guard_msgs (error, drop info) in
example : namesFrom widgetTree (4 - 3) 3 = rDrop 3 Widget.names := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  rLen Widget.names = 4
is false
-/
#guard_msgs (error, drop info) in
example : rLen Widget.names = 4 := by decide +kernel

end ProofLib.Testing.PlacedNamesTree
