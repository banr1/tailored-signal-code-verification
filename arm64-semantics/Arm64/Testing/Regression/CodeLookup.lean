/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import Arm64.Testing.Regression.CodeLookupShard0
public import Arm64.Testing.Regression.CodeLookupShard12
public import Arm64.Testing.Regression.CExamplesFixture

/-!
# Name-Based Code Layout Lookup

Regression tests for symbol-based offset, relocation, instruction, and fetch elaborators
(`code_off%`, `code_rel%`, `code_lemma%`, `nat_lit%`, `code_fetches_fn`, `reloc_call_off%`,
`reloc_call_insns%`, `words_ret_off%`, `words_insn_off%`, and `code_call_off%`).
-/

@[expose] public section

namespace Testing.CodeLookup

open Arm64 ProofLib Testing.CExamplesFixture

/-! ## Numerals -/

example : code_off% cExamplesCode "c_max_u64" = 12 := rfl
example : code_off% cExamplesCode "c_swap_u64" = 24 := rfl
example : code_rel% cExamplesCode "c_max_u64" "c_swap_u64" = 12 := rfl

-- At `BitVec 64` the result is literally `BitVec.ofNat 64 k` (the term `k#64` denotes).
#guard_expr (code_rel% cExamplesCode "c_arith_shift" "c_swap_u64" : BitVec 64) =ₛ 24#64
-- Expected type propagated through `+` (as in `mid := entry + code_rel% ...`).
example (entry : BitVec 64) :
    entry + code_rel% cExamplesCode "c_arith_shift" "c_max_u64" = entry + 12#64 := rfl
-- Under `binop%` (no expected type at the leaf) the result is still syntactically
-- `BitVec.ofNat 64 k`, not an `OfNat` numeral.
#guard_expr (fun entry : BitVec 64 => entry + code_rel% cExamplesCode "c_arith_shift" "c_max_u64")
  =ₛ (fun entry : BitVec 64 => entry + 12#64)
#guard_expr (fun entry : BitVec 64 => entry + code_off% cExamplesCode "c_swap_u64")
  =ₛ (fun entry : BitVec 64 => entry + 24#64)
#guard_expr (fun entry : BitVec 64 => code_off% cExamplesCode "c_swap_u64" + entry)
  =ₛ (fun entry : BitVec 64 => 24#64 + entry)
#guard_expr (fun entry : BitVec 64 =>
    entry + code_off% cExamplesCode "c_max_u64" + code_rel% cExamplesCode "c_max_u64" "c_swap_u64")
  =ₛ (fun entry : BitVec 64 => entry + 12#64 + 12#64)
#guard_expr (fun entry : BitVec 64 => entry - code_off% cExamplesCode "c_swap_u64")
  =ₛ (fun entry : BitVec 64 => entry - 24#64)
#guard_expr (fun entry : BitVec 64 => entry + nat_lit% (code_off% cExamplesCode "c_swap_u64" + 4))
  =ₛ (fun entry : BitVec 64 => entry + 28#64)
-- With no `BitVec` context the result stays an `OfNat` numeral defaulting to `Nat`.
#guard_expr (fun n : Nat => n + code_off% cExamplesCode "c_swap_u64") =ₛ (fun n : Nat => n + 24)
#guard_expr (code_off% cExamplesCode "c_swap_u64" + 1) =ₛ (24 + 1 : Nat)

/-! ## Positive: `nat_lit%` -/

example : (nat_lit% (2^64 - code_rel% cExamplesCode "c_arith_shift" "c_max_u64") : Nat) =
    18446744073709551604 := rfl
#guard_expr (nat_lit% (2^64 - code_rel% cExamplesCode "c_arith_shift" "c_max_u64") : BitVec 64)
  =ₛ 18446744073709551604#64

/-! ## Positive: lemmas -/

example : cExamplesCode.fnOff "c_max_u64" = 12 := code_lemma% cExamplesCode fnOff "c_max_u64"
example : cExamplesCode.fnOff "c_max_u64" = 12 := code_lemma% cExamplesCode off "c_max_u64"
example : Obj.fnSize cExamplesImage "c_swap_u64" = 20 :=
  code_lemma% cExamplesCode fnSize "c_swap_u64"
#guard_expr code_lemma% cExamplesCode fnOff "c_swap_u64" =ₛ cExamplesCode_fnOff_0x18

/-! ## Positive: `code_fetches_fn` adds the same hypotheses as `code_fetches` -/

example (b : BitVec 64) (H : String → Option (State → State)) : True := by
  code_fetches_fn cExamplesCode cExamplesBin b H "c_swap_u64"
  -- `c_swap_u64` is 20 bytes: 5 fetch hypotheses, the last at `k = 16`.
  have _h : ∃ i, (cExamplesCode.rebase b H).fetch
      ((cExamplesCode.rebase b H).fnAddr "c_swap_u64" + 16#64) = i := ⟨_, by assumption⟩
  trivial

/-! ## Negative -/

/-- error: code lookup: no `fnOff`/`stubOff` lemma for symbol "c_nope" of `Testing.CExamplesFixture.cExamplesCode` (is the symbol in the image, and is its name spelled exactly as in the generated `*Code.lean` / `*Index.json`?) -/
#guard_msgs in
example : (code_off% cExamplesCode "c_nope" : Nat) = 0 := rfl

/-- error: code_rel%: "c_arith_shift" (offset 0) precedes "c_max_u64" (offset 12) -/
#guard_msgs in
example : (code_rel% cExamplesCode "c_max_u64" "c_arith_shift" : Nat) = 0 := rfl

/-- error: code lookup: unknown kind `bogus` (expected fnOff, stubOff, off, fnSize, frameBytes or hookAtOff) -/
#guard_msgs in
example : cExamplesCode.fnOff "c_max_u64" = 12 := code_lemma% cExamplesCode bogus "c_max_u64"

/-- error: nat_lit%: x is not a closed `Nat` term -/
#guard_msgs in
example (x : Nat) : (nat_lit% x : Nat) = x := rfl

/-! ## Call and instruction offset elaborators -/

def sampleCallRelocs : Array Obj.RelocEntry :=
  #[ { off := 0,  kind := .adrpHi21,  sym := "global_tbl", addend := 0 }
   , { off := 4,  kind := .ldst64Lo12, sym := "global_tbl", addend := 0 }
   , { off := 12, kind := .call26,    sym := "callee_a",   addend := 0 }
   , { off := 24, kind := .call26,    sym := "callee_b",   addend := 0 }
   , { off := 36, kind := .call26,    sym := "callee_a",   addend := 0 } ]

-- Default elaboration is `BitVec.ofNat 64 n` (`=ₛ n#64`), working inside `entry + reloc_call_off% ...`
-- and `(reloc_call_off% ...).toNat / 4` without type annotations.
#guard_expr (reloc_call_off% sampleCallRelocs "callee_a") =ₛ 12#64
#guard_expr (reloc_call_off% sampleCallRelocs "callee_b") =ₛ 24#64
#guard_expr (reloc_call_off% sampleCallRelocs "callee_a" 1) =ₛ 36#64
#guard_expr (fun entry : BitVec 64 => entry + reloc_call_off% sampleCallRelocs "callee_a")
  =ₛ (fun entry : BitVec 64 => entry + 12#64)
#guard_expr (fun entry : BitVec 64 => entry + reloc_call_off% sampleCallRelocs "callee_a" 1)
  =ₛ (fun entry : BitVec 64 => entry + 36#64)

example : (reloc_call_off% sampleCallRelocs "callee_a").toNat / 4 = 3 := rfl
example : (reloc_call_off% sampleCallRelocs "callee_a" 1 : Nat) = 36 := rfl
example : reloc_call_insns% sampleCallRelocs "callee_a" = 3 := rfl
example : reloc_call_insns% sampleCallRelocs "callee_a" 1 = 9 := rfl

example : Obj.findCallOff sampleCallRelocs "callee_a" = 12#64 := rfl
example : Obj.findCallOff sampleCallRelocs "callee_a" 1 = 36#64 := rfl
example : Obj.findCallOff? sampleCallRelocs "missing" = none := rfl

def sampleWordsArr : Array (BitVec 32) :=
  #[ 0xa9bf7bfd#32  -- +0:  stp x29, x30, [sp, #-16]!
   , 0xb4000060#32  -- +4:  cbz x0, +12
   , 0x94000010#32  -- +8:  bl +0x40 (targets entry + 0x48)
   , 0xd65f03c0#32  -- +12: ret
   , 0x9400000e#32  -- +16: bl +0x38 (targets entry + 0x48)
   , 0x9400001c#32  -- +20: bl +0x70 (targets entry + 0x84)
   , 0xd65f03c0#32  -- +24: ret
   ]

#guard_expr (words_ret_off% sampleWordsArr) =ₛ 12#64
#guard_expr (words_ret_off% sampleWordsArr 1) =ₛ 24#64
#guard_expr (words_condbr_off% sampleWordsArr) =ₛ 4#64
#guard_expr (words_insn_off% sampleWordsArr "ret" 1) =ₛ 24#64
#guard_expr (words_insn_off% sampleWordsArr "bl" 2) =ₛ 20#64
#guard_expr (words_insn_off% sampleWordsArr 0xd65f03c0#32 1) =ₛ 24#64

example : Obj.findRetOff sampleWordsArr 0 = 12#64 := rfl
example : Obj.findRetOff sampleWordsArr 1 = 24#64 := rfl
example : Obj.findCondBrOff sampleWordsArr 0 = 4#64 := rfl

def sampleCodeTree : CodeTree :=
  ProgramReflection.WordTree.ofWordsArray sampleWordsArr

-- `code_call_off%` and `code_call_addr%` on `CodeTree` (`WordTree`):
-- At `entry = 0x1000#64`, `+8` (`0x94000010`) and `+16` (`0x9400000e`) both `BL` to `0x1048#64`,
-- and `+20` (`0x9400001c`) `BL`s to `0x1084#64`.
#guard_expr (code_call_off% sampleCodeTree 0x1000#64 0x1048#64) =ₛ 8#64
#guard_expr (code_call_off% sampleCodeTree 0x1000#64 0x1048#64 1) =ₛ 16#64
#guard_expr (code_call_off% sampleCodeTree 0x1000#64 0x1084#64) =ₛ 20#64
example :
    code_call_addr% sampleCodeTree 0x1000#64 0x1048#64 1 = 0x1000#64 + 16#64 := rfl
example : Obj.findBlOff sampleCodeTree 0x1000#64 0x1048#64 1 = 16#64 := rfl

/-! ## Negative: `reloc_call_off%`, `words_ret_off%`, `code_call_off%` -/

/-- error: reloc_call_off%: no call/branch relocation targeting "no_such_callee" (available call symbols: "callee_a", "callee_b") -/
#guard_msgs in
example : (reloc_call_off% sampleCallRelocs "no_such_callee" : BitVec 64) = 0#64 := rfl

/-- error: reloc_call_off%: occurrence index 2 out of range for symbol "callee_a" (found 2 call(s) at byte offset(s) [12, 36]) -/
#guard_msgs in
example : (reloc_call_off% sampleCallRelocs "callee_a" 2 : BitVec 64) = 0#64 := rfl

/-- error: code_call_off%: no BL/B call targeting `4352#64` (displacement 0x100) found in function (calls in function: +8 -> 0x1048, +16 -> 0x1048, +20 -> 0x1084) -/
#guard_msgs in
example : (code_call_off% sampleCodeTree 0x1000#64 0x1100#64 : BitVec 64) = 0#64 := rfl

/-! ## Positive & negative: multi-module sharded `<Name>Shard0..k` lookup -/

section ShardedLookup
open Testing.CodeLookupSharded

example : code_off% widgetCode "widget_entry" = 0 := rfl
example : code_off% widgetCode "widget_far" = 32 := rfl
example : code_off% widgetCode "widget_stub" = 64 := rfl
example : code_rel% widgetCode "widget_entry" "widget_far" = 32 := rfl
example : widgetCode.fnOff "widget_far" = 32 := code_lemma% widgetCode fnOff "widget_far"
example : widgetCode.fnOff "widget_stub" = 64 := code_lemma% widgetCode stubOff "widget_stub"

/-- error: code lookup: no `fnOff`/`stubOff` lemma for symbol "widget_missing" of `Testing.CodeLookupSharded.widgetCode` (is the symbol in the image, and is its name spelled exactly as in the generated `*Code.lean` / `*Index.json`?) -/
#guard_msgs in
example : (code_off% widgetCode "widget_missing" : Nat) = 0 := rfl

end ShardedLookup

end Testing.CodeLookup
