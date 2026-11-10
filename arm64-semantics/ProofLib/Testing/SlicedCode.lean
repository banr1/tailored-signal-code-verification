/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Hooks
public import ProofLib.ObjectLoad
public import ProofLib.ProgramReflection

/-!
# `.text`-Sliced Image and `subroutine_ok_ofImage` Tests

Regression tests for `.text`-sliced program rebasing (`Program.ofImage_take_eq_rebase`,
`Program.codeLoaded_rebase_take_of_loaded`), `subroutine_ok_ofImage`, and sliced `WordTree`
metadata queries (`fnSize_of_wordTree_take`, `fnFrameBytes_of_wordTree_take`).
-/

@[expose] public section

namespace Examples.Testing.ProofLib.SlicedCode

open Arm64 _root_.ProofLib _root_.ProofLib.ProgramReflection

/-- Synthetic linked image with a 4-byte `RET` function `alpha` at offset `0` and a 4-byte
    external stub `ext_fn` at offset `4`. -/
def alphaImage : Obj.LinkedImage where
  objects := [{ name := "alpha", fns := [("alpha", [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8])] }]
  code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]
  dataOff := 0x1000
  data := []
  bss := 0
  roData := []
  externData := []
  gotOff := 0x1000
  got := []
  relocs := []
  symbols := [("alpha", 0)]
  stubs := [("ext_fn", 4)]

abbrev alphaCodeTextEnd : Nat := 4

def alphaCode : Program :=
  { alphaImage.toProgram with code := alphaImage.code.take alphaCodeTextEnd }

theorem alphaCode_canonical :
    { alphaImage.toProgram with code := alphaImage.code.take alphaCodeTextEnd } = alphaCode := rfl

def alphaCode_tree : WordTree := word_tree_of% alphaCode

theorem alphaCode_code_eq : alphaCode.code = alphaCode_tree.toBytes := by rfl_kernel
theorem alphaCode_tree_size : alphaCode_tree.checkSize? = some 1 := by rfl_kernel

def alphaCode_funcTable : List (String × (Nat × Nat)) := Obj.funcTable alphaImage
def alphaCode_funcChars : List (List Char × (Nat × Nat)) :=
  assoc_chars_of% alphaCode_funcTable

theorem alphaCode_funcTable_eq :
    alphaCode_funcTable = toStringAssoc alphaCode_funcChars := by rfl_kernel

theorem alphaCode_funcTable_fresh : allFreshCharAssoc alphaCode_funcChars = true := by rfl_kernel

theorem alphaCode_ofImage {img : Obj.Image} {X O : String → Option (State → State)}
    (h : Obj.Loads alphaImage img) :
    { Program.ofImage img X O with code := img.code.take alphaCodeTextEnd } =
      alphaCode.rebase img.base X O :=
  Program.ofImage_take_eq_rebase alphaCode_canonical h

theorem alphaCode_codeLoaded {img : Obj.Image} {s : State} {X O : String → Option (State → State)}
    (h : Obj.Loads alphaImage img) (hL : img.Loaded s) :
    (alphaCode.rebase img.base X O).CodeLoaded s.mem :=
  Program.codeLoaded_rebase_take_of_loaded alphaCode_canonical h hL

example {img : Obj.Image} (h : Obj.Loads alphaImage img)
    (H : String → Option (State → State)) (spec : Spec Unit)
    (hsub : subroutine_ok (alphaCode.rebase img.base H)
      ((alphaCode.rebase img.base H).fnAddr "alpha") spec) :
    let prog := { Program.ofImage img H with code := img.code.take alphaCodeTextEnd }
    subroutine_ok prog (prog.fnAddr "alpha") spec :=
  subroutine_ok_ofImage img H "alpha" spec (alphaCode_ofImage h) hsub

theorem alphaCode_fnSize_0x0 : Obj.fnSize alphaImage "alpha" = 4 :=
  fnSize_of_wordTree_take alphaImage alphaCode_code_eq alphaCode_tree_size alphaCode_funcChars
    alphaCode_funcTable_eq alphaCode_funcTable_fresh 0 4 (by rfl_kernel) (by rfl_kernel)

theorem alphaCode_frameBytes_0x0 : fnFrameBytes alphaImage "alpha" = 0 :=
  fnFrameBytes_of_wordTree_take alphaImage alphaCode_code_eq alphaCode_tree_size alphaCode_funcChars
    alphaCode_funcTable_eq alphaCode_funcTable_fresh 0 0 (by rfl_kernel) (by rfl_kernel)

/--
error: could not synthesize default value for parameter 'hm' using tactics
---
error: Tactic `rfl` failed: The left-hand side
  4 * 1
is not definitionally equal to the right-hand side
  8

hbad : List.take 8 alphaImage.code = alphaCode_tree.toBytes
⊢ 4 * 1 = 8
-/
#guard_msgs in
example (hbad : alphaImage.code.take 8 = alphaCode_tree.toBytes) :
    Obj.fnSize alphaImage "alpha" = 4 :=
  fnSize_of_wordTree_take alphaImage hbad alphaCode_tree_size alphaCode_funcChars
    alphaCode_funcTable_eq alphaCode_funcTable_fresh 0 4 (by rfl_kernel) (by rfl_kernel)

end Examples.Testing.ProofLib.SlicedCode
