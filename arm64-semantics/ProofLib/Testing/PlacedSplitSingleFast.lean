/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.SplitSingleFast
public import ProofLib.Testing.PlacedSplitSingle

/-!
# Symbol-Tree Chunked Single-Block Placement Check

Regression tests for `ProofLib.Placed.SplitSingleFast`: chunked symbol-tree and text-walk
placement checks (`symTreeOkChunk`, `textOkChunkT`, `checkDisjoint_spec_chunksT`) on `Gadget`,
plus negative `#guard_msgs` tests for malformed symbol trees and text chunks.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib.Testing.PlacedSplitSingleFast

open Arm64 Arm64.Process Arm64.Obj Arm64.Obj.Interned ProofLib.ProgramReflection ProofLib.ObjectLoad
  ProofLib.Placed.Split ProofLib.Testing.PlacedSplitSingle

/-- The slots of `Gadget` under `ly`: `f` (index 2) is the block symbol at offset 0; the others are
    resolved at their `ly.addrs` entries. -/
def tree : VecTree SymSlot :=
  .node 2 (.node 1 (.node 0 .leaf ⟨true, 0x410000#64, 0x410000#64⟩ .leaf)
      ⟨true, 0x500000#64, 0x500000#64⟩ .leaf)
    ⟨false, 0#64, 0x400000#64⟩
    (.node 1 (.node 0 .leaf ⟨true, 0x401004#64, 0x401004#64⟩ .leaf)
      ⟨true, 0x401000#64, 0x401000#64⟩ .leaf)

theorem sym0 : symTreeOkChunk Gadget ly tree 0 3 = true := by decide +kernel
theorem sym1 : symTreeOkTail Gadget ly tree 3 = true := by decide +kernel

theorem text0T : textOkChunkT Gadget ly tree rl 0 false 0 8 true 2 = true := by decide +kernel
theorem text1T : textOkChunkT Gadget ly tree rl 8 true 2 16 false 4 = true := by decide +kernel
theorem text2T : textOkTailT Gadget ly tree rl 16 false 4 = true := by decide +kernel

theorem gadget_checkedT : Gadget.toLib.Placeable (ly.toPlacement Gadget.names) ∧
    Gadget.toLib.InElf img (ly.toPlacement Gadget.names) ∧
    Gadget.toLib.DataDisjoint (ly.toPlacement Gadget.names) :=
  checkDisjoint_spec_chunksT (symChars := symChars) rfl rfl segLens_eq chk_nodup chk_ids
    chk_ptext chk_pdata (symTreeOkChunks_cons sym0 (symTreeOkChunks_nil sym1))
    (textOkChunksT_cons text0T (textOkChunksT_cons text1T (textOkChunksT_nil text2T)))
    (dataOkChunks_cons data0 (dataOkChunks_nil data1)) chk_exports chk_ddisj

/-- `tree` with `ext` (index 1) resolved one word past its `ly.addrs` entry. -/
def treeBad : VecTree SymSlot :=
  .node 2 (.node 1 (.node 0 .leaf ⟨true, 0x410000#64, 0x410000#64⟩ .leaf)
      ⟨true, 0x500000#64, 0x500004#64⟩ .leaf)
    ⟨false, 0#64, 0x400000#64⟩
    (.node 1 (.node 0 .leaf ⟨true, 0x401004#64, 0x401004#64⟩ .leaf)
      ⟨true, 0x401000#64, 0x401000#64⟩ .leaf)

/--
error: Tactic `decide` proved that the proposition
  symTreeOkChunk Gadget ly treeBad 0 3 = true
is false
-/
#guard_msgs (error, drop info) in
example : symTreeOkChunk Gadget ly treeBad 0 3 = true := by decide +kernel

/-- `tree` without the slot of `tab` (index 4). -/
def treeShort : VecTree SymSlot :=
  .node 2 (.node 1 (.node 0 .leaf ⟨true, 0x410000#64, 0x410000#64⟩ .leaf)
      ⟨true, 0x500000#64, 0x500000#64⟩ .leaf)
    ⟨false, 0#64, 0x400000#64⟩
    (.node 0 .leaf ⟨true, 0x401004#64, 0x401004#64⟩ .leaf)

/--
error: Tactic `decide` proved that the proposition
  symTreeOkTail Gadget ly treeShort 3 = true
is false
-/
#guard_msgs (error, drop info) in
example : symTreeOkTail Gadget ly treeShort 3 = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  textOkChunkT Gadget ly treeBad rl 0 false 0 8 true 2 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunkT Gadget ly treeBad rl 0 false 0 8 true 2 = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  textOkChunkT Gadget ly tree rl 0 false 0 8 false 2 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunkT Gadget ly tree rl 0 false 0 8 false 2 = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  textOkChunkT Gadget ly tree rl 0 false 0 8 true 3 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunkT Gadget ly tree rl 0 false 0 8 true 3 = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  textOkChunkT Gadget ly tree rlBad 8 true 2 16 false 4 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunkT Gadget ly tree rlBad 8 true 2 16 false 4 = true := by decide +kernel

end ProofLib.Testing.PlacedSplitSingleFast

end
