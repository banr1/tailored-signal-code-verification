/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.ExternSymtab

/-!
# `ExternSymtab` Regression Tests

Positive and negative `decide +kernel` tests for `externSymtab_of` and `externSymtabOk` over a
three-name interned table and `.symtab` fixture.
-/

@[expose] public section

namespace Examples.Testing.PlacedExternSymtabTest

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process ProofLib ProofLib.ObjectLoad
  ProofLib.ProgramReflection

/-- Names table (strictly increasing): `alpha` = 0, `ext` = 1, `widget` = 2. -/
def nameChars : List (List Char) := [['a', 'l', 'p', 'h', 'a'], ['e', 'x', 't'],
  ['w', 'i', 'd', 'g', 'e', 't']]

def names : List String := nameChars.map String.ofList

/-- `.symtab`: `ext` once, `widget` twice. -/
def symChars : List (List Char × BitVec 64) :=
  [(['e', 'x', 't'], 0x500000#64), (['w', 'i', 'd', 'g', 'e', 't'], 0x400000#64),
   (['w', 'i', 'd', 'g', 'e', 't'], 0x400010#64)]

def img : ElfImage where
  entry := 0x400000#64
  phdrVaddr := 0x400040#64
  phnum := 0
  segments := []
  brkStart := 0x420000#64
  symbols := toStringAssoc symChars

def ly : Layout := { base := 0x400000#64, addrs := [0#64, 0x500000#64, 0x400000#64] }

theorem ext_symtab : ∀ i ∈ [1], lookupUnique (names.getD i "") img.symbols =
    some (ly.addrs.getD (names.idxOf (names.getD i "")) 0#64) :=
  externSymtab_of (symChars := symChars) rfl rfl (by decide +kernel)

example : lookupUnique "ext" img.symbols = some ((ly.toPlacement names).ρ "ext") :=
  ext_symtab 1 (by simp)

/--
error: Tactic `decide` proved that the proposition
  externSymtabOk [0#64, 4194304#64, 4194304#64] nameChars [1] (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : externSymtabOk [0#64, 0x400000#64, 0x400000#64] nameChars [1]
    (prepareCharAssocVal symChars) = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  externSymtabOk ly.addrs nameChars [0] (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : externSymtabOk ly.addrs nameChars [0] (prepareCharAssocVal symChars) = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  externSymtabOk ly.addrs nameChars [2] (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : externSymtabOk ly.addrs nameChars [2] (prepareCharAssocVal symChars) = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  externSymtabOk ly.addrs nameChars [3] (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : externSymtabOk ly.addrs nameChars [3] (prepareCharAssocVal symChars) = true := by
  decide +kernel

end Examples.Testing.PlacedExternSymtabTest

end
