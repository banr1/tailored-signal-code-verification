/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.RelocFnGen
public import ProofLib.Testing.LayoutGenericRelocs

/-!
# Tests for `ProofLib.RelocFnGen`

Positive and `#guard_msgs` negative regression tests for `gen_reloc_fn`, `gen_reloc_fn_index`,
`obj_mem`, and relocation-free transfer (`Obj.Loads.subroutineOk_of_relocFreeFn`).
-/

set_option autoImplicit false

@[expose] public section

namespace Testing.RelocFnGenTest

open Arm64 ProofLib Testing.LayoutGenericRelocs

/-! ## Generated literals match hand-written literals -/

gen_reloc_fn genBump testRelocObj "bump_counter" in testLinkedImage

example : genBumpRelocs = bumpCounterRelocs := by decide
example : genBumpWords = bumpCounterWords := by decide
example : checkRelocFn testRelocObj "bump_counter" genBumpRelocs genBumpWords = true :=
  genBump_check
example : testRelocObj ∈ testLinkedImage.objects := genBump_mem

/-! ## No `_mem` theorem without `in <image>` -/

gen_reloc_fn genMagic testRelocObj "read_ro_magic"

example : genMagicRelocs = readRoMagicRelocs := by decide
example : genMagicWords = readRoMagicWords := by decide

/-- error: Unknown identifier `genMagic_mem` -/
#guard_msgs in
example : testRelocObj ∈ testLinkedImage.objects := genMagic_mem

/-! ## `obj_mem` on a non-head element -/

example : (3 : Nat) ∈ [1, 2, 3] := by obj_mem

/-! ## Unknown symbol, fuzzy `did you mean`, and relocation-free hint -/

/--
error: gen_reloc_fn: no `relocFns` entry named "no_such_fn"; available: [bump_counter, read_ro_magic]
-/
#guard_msgs in
gen_reloc_fn genMissing testRelocObj "no_such_fn"

/-- Minimal relocation-free object fixture implementing `ret42` (`mov x0, #42; ret`). -/
def ret42Obj : Obj.ObjectInfo where
  name := "ret42.o"
  fns := [("ret42", [0x40#8, 0x05#8, 0x80#8, 0xd2#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8])]

/-- Linked image fixture of `ret42.o`. -/
def ret42Linked : Obj.LinkedImage where
  code := [0x40#8, 0x05#8, 0x80#8, 0xd2#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8]
  dataOff := 0x1000
  data := []
  gotOff := 0x1000
  symbols := [("ret42", 0)]
  objSymbols := [("ret42.o", [("ret42", 0)])]
  stubs := []
  objects := [ret42Obj]

def ret42Spec : Spec Unit where
  pre := fun () _ => emp
  post := fun () _ sf => ⌜sf.readReg64 .x0 = 42#64⌝

/--
error: gen_reloc_fn: no `relocFns` entry named "ret42"; available: []
note: "ret42" is already in obj.fns (relocation-free) — use obj.fns directly; gen_reloc_fn is not needed
-/
#guard_msgs in
gen_reloc_fn genRelocFreeExact ret42Obj "ret42"

/--
error: gen_reloc_fn: no `relocFns` entry named "_ret4"; available: []
note: "ret42" is already in obj.fns (relocation-free) — use obj.fns directly; gen_reloc_fn is not needed
-/
#guard_msgs in
gen_reloc_fn genRelocFreeStem ret42Obj "_ret4"

def testManyRelocObj : Obj.ObjectInfo where
  name := "alpha_static.o"
  fns := [("alpha_leaf_fast [alpha_static]", [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8])]
  callFns := []
  relocFns :=
    [ { sym := "alpha_stub_0", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "alpha_stub_1", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "alpha_stub_2", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "alpha_stub_3", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "alpha_stub_4", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "alpha_stub_5", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "alpha_stub_6", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "alpha_stub_7", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "_alpha_os_prim_alloc_slow [alpha_static]", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "_alpha_os_prim_alloc [alpha_static]", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] } ]

/--
error: gen_reloc_fn: no `relocFns` entry named "_alpha_os_prim_alloc"; did you mean: ["_alpha_os_prim_alloc [alpha_static]", "_alpha_os_prim_alloc_slow [alpha_static]"]; available (first 8 of 10): [alpha_stub_0, alpha_stub_1, alpha_stub_2, alpha_stub_3, alpha_stub_4, alpha_stub_5, alpha_stub_6, alpha_stub_7]
-/
#guard_msgs in
gen_reloc_fn genPrimAlloc testManyRelocObj "_alpha_os_prim_alloc"

/--
error: gen_reloc_fn: no `relocFns` entry named "READ_RO"; did you mean: ["read_ro_magic"]; available: [bump_counter, read_ro_magic]
-/
#guard_msgs in
gen_reloc_fn genReadRoCase testRelocObj "READ_RO"

/--
error: gen_reloc_fn: no `relocFns` entry named "alpha_leaf_fast"; available (first 8 of 10): [alpha_stub_0, alpha_stub_1, alpha_stub_2, alpha_stub_3, alpha_stub_4, alpha_stub_5, alpha_stub_6, alpha_stub_7]
note: "alpha_leaf_fast [alpha_static]" is already in obj.fns (relocation-free) — use obj.fns directly; gen_reloc_fn is not needed
-/
#guard_msgs in
gen_reloc_fn genLeafFast testManyRelocObj "alpha_leaf_fast"

/-! ## `obj_mem` on an absent element -/

/--
error: obj_mem: element not found in list
  4
-/
#guard_msgs in
example : (4 : Nat) ∈ [1, 2, 3] := by obj_mem

/-! ## Relocation-free (`o.fns`) transfer -/

def ret42Words : List (BitVec 32) := [0xd2800540#32, 0xd65f03c0#32]

theorem ret42_hasWords_ok (prog : Program) (a : BitVec 64) (hw : prog.hasWords a ret42Words) :
    subroutine_ok prog a ret42Spec := by
  unfold ret42Words at hw
  wp_init x s0
  wp_steps
  wp_done

example {img : Obj.Image} {H : String → Option (State → State)}
    (hl : Obj.Loads ret42Linked img) :
    (Program.ofImage img H).subroutineOk "ret42" ret42Spec :=
  Obj.Loads.subroutineOk_of_relocFreeFn (o := ret42Obj) (words := ret42Words) hl
    (by obj_mem) (by decide) (by decide)
    fun a hw => ret42_hasWords_ok _ a hw

/-! ## Indexed `O(log F)` lookup, hash collisions, and duplicate guard -/

section IndexedLookup

open ProofLib.ProgramReflection

/-- Three distinct symbols falling into the same bucket of `hashChars1024`. -/
theorem hash_collision_triple :
    hashChars1024 "col_az".toList = hashChars1024 "col_ib".toList ∧
    hashChars1024 "col_ib".toList = hashChars1024 "col_qJ".toList := by
  decide +kernel

def collisionRelocObj : Obj.ObjectInfo where
  name := "collision.o"
  relocFns :=
    [ { sym := "col_az", code := wordsToBytesLE bumpCounterWords, relocs := bumpCounterRelocs }
    , { sym := "col_ib", code := wordsToBytesLE readRoMagicWords, relocs := readRoMagicRelocs } ]

gen_reloc_fn_index collisionObjIdx collisionRelocObj

example : collisionObjIdx.lookupIdx "col_az" = some 0 := by decide +kernel
example : collisionObjIdx.lookupIdx "col_ib" = some 1 := by decide +kernel

example : collisionObjIdx.lookupIdx "col_qJ" = none := by decide +kernel
example : collisionObjIdx.check "col_qJ" bumpCounterRelocs bumpCounterWords = false := by
  decide +kernel
example : collisionObjIdx.checkWordsAt 0 readRoMagicWords = false := by
  decide +kernel

gen_reloc_fn genColAz collisionRelocObj "col_az"
gen_reloc_fn genColIb collisionRelocObj "col_ib" using collisionObjIdx

example : checkRelocFn collisionRelocObj "col_az" genColAzRelocs genColAzWords = true :=
  genColAz_check
example : collisionRelocObj.RelocFnChecked "col_az" genColAzRelocs genColAzWords :=
  genColAz_checked
example : checkRelocFn collisionRelocObj "col_ib" genColIbRelocs genColIbWords = true :=
  genColIb_check
example : collisionRelocObj.RelocFnChecked "col_ib" genColIbRelocs genColIbWords :=
  genColIb_checked

def dupRelocObj : Obj.ObjectInfo where
  name := "dup.o"
  relocFns :=
    [ { sym := "dup_fn", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "other_fn", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }
    , { sym := "dup_fn", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] } ]

/--
error: gen_reloc_fn_index: duplicate symbol "dup_fn" in `dupRelocObj.relocFns` (indices 0 and 2)
-/
#guard_msgs in
gen_reloc_fn_index dupObjIdx dupRelocObj

end IndexedLookup

end Testing.RelocFnGenTest
