/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib

/-!
# Functional Correctness Regression Suite

Proves `subroutineOk` contracts for five reference A64 subroutines (`divmod_u64`,
`bswap_and_clz_u64`, `add128_u64`, `smaddl_sdiv_i64`, and `stack_spill_struct_update`),
both placement-independently via `FnCode.holds` and on standalone and linked programs.
-/

@[expose] public section

namespace Testing.FunctionalCorrectness

open Arm64
open ProofLib

set_option maxRecDepth 200000

/-! ## Unsigned division and remainder (`divmod_u64`) -/

@[simp, arm64_norm] def divmodU64_addr : BitVec 64 := 0x20000#64

def divmodU64Prog : Program :=
  Program.ofWords 0x1000#64 [
    0x9ac10802#32, -- .dataProc2 .W64 .UDIV .x2 .x0 .x1
    0x9b018041#32, -- .dataProc3 .W64 .MSUB .x1 .x2 .x1 .x0
    0xaa0203e0#32, -- .logicalReg .W64 .ORR .x0 .xzr .x2 .LSL 0
    0xd65f03c0#32  -- .br false true .lr
  ] [("divmod_u64", 0x1000#64)]

def divmodU64FnCode : FnCode :=
  FnCode.ofFn "divmod_u64"
    ("9ac10802 " ++ -- udiv x2, x0, x1
     "9b018041 " ++ -- msub x1, x2, x1, x0
     "aa0203e0 " ++ -- mov  x0, x2
     "d65f03c0")    -- ret

abbrev DivModU64CodeAt (prog : Program) : Prop :=
  divmodU64FnCode.holds prog

c_spec divmodU64Spec (a : u64) (b : u64) : u64
  returns      a / b
  ensures_pure sf.readReg64 .x1 = a - (a / b) * b ∧
               sf.readReg64 .x0 = (if b == 0#64 then 0#64 else a / b)

/-! ## Byte swap, leading zero count, bit reversal, and bitfields (`bswap_and_clz_u64`) -/

@[simp, arm64_norm] def bswapAndClzU64_addr : BitVec 64 := 0x20010#64

def bswapAndClzU64Prog : Program :=
  Program.ofWords 0x1000#64 [
    0xdac00c00#32, -- .dataProc1 .W64 .REV64 .x0 .x0
    0xdac01001#32, -- .dataProc1 .W64 .CLZ .x1 .x0
    0xdac00002#32, -- .dataProc1 .W64 .RBIT .x2 .x0
    0xd3485c03#32, -- .bitfield .W64 .UBFM .x3 .x0 8 23
    0x93483c04#32, -- .bitfield .W64 .SBFM .x4 .x0 8 15
    0xd65f03c0#32  -- .br false true .lr
  ] [("bswap_and_clz_u64", 0x1000#64)]

def bswapAndClzU64FnCode : FnCode :=
  FnCode.ofFn "bswap_and_clz_u64"
    ("dac00c00 " ++ -- rev  x0, x0
     "dac01001 " ++ -- clz  x1, x0
     "dac00002 " ++ -- rbit x2, x0
     "d3485c03 " ++ -- ubfx x3, x0, #8, #16
     "93483c04 " ++ -- sbfx x4, x0, #8, #8
     "d65f03c0")    -- ret

abbrev BswapAndClzU64CodeAt (prog : Program) : Prop :=
  bswapAndClzU64FnCode.holds prog

c_spec bswapAndClzU64Spec (x : u64) : u64
  let swapped := rev64 x
  returns      swapped
  ensures_pure sf.readReg64 .x1 = BitVec.ofNat 64 (countLeadingZeros swapped) ∧
               sf.readReg64 .x2 = reverseBits swapped ∧
               sf.readReg64 .x3 = (swapped.extractLsb' 8 16).zeroExtend 64 ∧
               sf.readReg64 .x4 = (swapped.extractLsb' 8 8).signExtend 64

/-! ## 128-bit addition with carry (`add128_u64`) -/

@[simp, arm64_norm] def add128U64_addr : BitVec 64 := 0x20028#64

def add128U64Prog : Program :=
  Program.ofWords 0x1000#64 [
    0xab020000#32, -- .addSubReg .W64 .ADDS .x0 .x0 .x2 .LSL 0
    0x9a030021#32, -- .addSubCarry .W64 .ADD .x1 .x1 .x3
    0xd65f03c0#32  -- .br false true .lr
  ] [("add128_u64", 0x1000#64)]

def add128U64FnCode : FnCode :=
  FnCode.ofFn "add128_u64"
    ("ab020000 " ++ -- adds x0, x0, x2
     "9a030021 " ++ -- adc  x1, x1, x3
     "d65f03c0")    -- ret

abbrev Add128U64CodeAt (prog : Program) : Prop :=
  add128U64FnCode.holds prog

c_spec add128U64Spec (lo_a : u64) (hi_a : u64) (lo_b : u64) (hi_b : u64) : u64
  returns      lo_a + lo_b
  ensures_pure sf.readReg64 .x1 = hi_a + hi_b + (if BitVec.ult (lo_a + lo_b) lo_a then 1#64 else 0#64) ∧
               (sf.readReg64 .x1 ++ sf.readReg64 .x0 : BitVec 128) = (hi_a ++ lo_a) + (hi_b ++ lo_b)

/-! ## Sign-extending multiply-accumulate and signed division (`smaddl_sdiv_i64`) -/

@[simp, arm64_norm] def smaddlSdivI64_addr : BitVec 64 := 0x20034#64

def smaddlSdivI64Prog : Program :=
  Program.ofWords 0x1000#64 [
    0x9b210804#32, -- .dataProc3 .W64 .SMADDL .x4 .x0 .x1 .x2
    0x9ac30c80#32, -- .dataProc2 .W64 .SDIV .x0 .x4 .x3
    0xf100009f#32, -- .addSubImm .W64 .SUBS .xzr .x4 0#64
    0x9a80a401#32, -- .condSelect .W64 .CSINC .x1 .x0 .x0 .GE
    0xda84a082#32, -- .condSelect .W64 .CSINV .x2 .x4 .x4 .GE
    0xd65f03c0#32  -- .br false true .lr
  ] [("smaddl_sdiv_i64", 0x1000#64)]

def smaddlSdivI64FnCode : FnCode :=
  FnCode.ofFn "smaddl_sdiv_i64"
    ("9b210804 " ++ -- smaddl x4, w0, w1, x2
     "9ac30c80 " ++ -- sdiv   x0, x4, x3
     "f100009f " ++ -- cmp    x4, #0
     "9a80a401 " ++ -- csinc  x1, x0, x0, ge
     "da84a082 " ++ -- csinv  x2, x4, x4, ge
     "d65f03c0")    -- ret

abbrev SmaddlSdivI64CodeAt (prog : Program) : Prop :=
  smaddlSdivI64FnCode.holds prog

c_spec smaddlSdivI64Spec (a : u64) (b : u64) (acc : i64) (div : i64) : i64
  let prod := acc + (a.truncate 32).signExtend 64 * (b.truncate 32).signExtend 64
  let quot := if div == 0#64 then 0#64 else BitVec.sdiv prod div
  returns      quot
  ensures_pure sf.readReg64 .x1 = (if BitVec.sle 0#64 prod then quot else quot + 1#64) ∧
               sf.readReg64 .x2 = (if BitVec.sle 0#64 prod then prod else ~~~prod)

/-! ## Stack frame spill/reload and struct update (`stack_spill_struct_update`) -/

@[simp, arm64_norm] def stackSpillStructUpdate_addr : BitVec 64 := 0x2004c#64

def stackSpillStructUpdateProg : Program :=
  Program.ofWords 0x1000#64 [
    0xa9be7bfd#32, -- .stp .W64 .fp .lr (.PreIndex .sp (-32#64))
    0xa90153f3#32, -- .stp .W64 .x19 .x20 (.Offset .sp 16#64)
    0xa9405013#32, -- .ldp .W64 false .x19 .x20 (.Offset .x0 0#64)
    0x8b010273#32, -- .addSubReg .W64 .ADD .x19 .x19 .x1 .LSL 0
    0xcb010294#32, -- .addSubReg .W64 .SUB .x20 .x20 .x1 .LSL 0
    0xa9005013#32, -- .stp .W64 .x19 .x20 (.Offset .x0 0#64)
    0x8b140260#32, -- .addSubReg .W64 .ADD .x0 .x19 .x20 .LSL 0
    0xa94153f3#32, -- .ldp .W64 false .x19 .x20 (.Offset .sp 16#64)
    0xa8c27bfd#32, -- .ldp .W64 false .fp .lr (.PostIndex .sp 32#64)
    0xd65f03c0#32  -- .br false true .lr
  ] [("stack_spill_struct_update", 0x1000#64)]

def stackSpillStructUpdateFnCode : FnCode :=
  FnCode.ofFn "stack_spill_struct_update"
    ("a9be7bfd " ++ -- stp x29, x30, [sp, #-32]!
     "a90153f3 " ++ -- stp x19, x20, [sp, #16]
     "a9405013 " ++ -- ldp x19, x20, [x0]
     "8b010273 " ++ -- add x19, x19, x1
     "cb010294 " ++ -- sub x20, x20, x1
     "a9005013 " ++ -- stp x19, x20, [x0]
     "8b140260 " ++ -- add x0, x19, x20
     "a94153f3 " ++ -- ldp x19, x20, [sp, #16]
     "a8c27bfd " ++ -- ldp x29, x30, [sp], #32
     "d65f03c0")    -- ret

abbrev StackSpillStructUpdateCodeAt (prog : Program) : Prop :=
  stackSpillStructUpdateFnCode.holds prog

c_spec stackSpillStructUpdateSpec
    (ptr : ptr) (delta : u64) (ghost f0 f1 : u64) (sp0 : sp) : u64
  requires     (ptr ↦₆₄ f0) ∗ ((ptr + 8#64) ↦₆₄ f1)
  ensures      (ptr ↦₆₄ (f0 + delta)) ∗ ((ptr + 8#64) ↦₆₄ (f1 - delta))
  preserves    stackFrame32At sp0
  returns      (f0 + delta) + (f1 - delta)
  ensures_pure sf.sp = sp0

/-! ## Linked program and proofs -/

def functionalCorrectnessCodeBundle : CodeBundle := [
  divmodU64FnCode,
  bswapAndClzU64FnCode,
  add128U64FnCode,
  smaddlSdivI64FnCode,
  stackSpillStructUpdateFnCode
]

def functionalCorrectnessLinkedProg : Program :=
  Program.ofWords 0x20000#64 [
    -- 0x20000: divmod_u64
    0x9ac10802#32, 0x9b018041#32, 0xaa0203e0#32, 0xd65f03c0#32,
    -- 0x20010: bswap_and_clz_u64
    0xdac00c00#32, 0xdac01001#32, 0xdac00002#32, 0xd3485c03#32, 0x93483c04#32, 0xd65f03c0#32,
    -- 0x20028: add128_u64
    0xab020000#32, 0x9a030021#32, 0xd65f03c0#32,
    -- 0x20034: smaddl_sdiv_i64
    0x9b210804#32, 0x9ac30c80#32, 0xf100009f#32, 0x9a80a401#32, 0xda84a082#32, 0xd65f03c0#32,
    -- 0x2004c: stack_spill_struct_update
    0xa9be7bfd#32, 0xa90153f3#32, 0xa9405013#32, 0x8b010273#32, 0xcb010294#32,
    0xa9005013#32, 0x8b140260#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32
  ] [
    ("divmod_u64", divmodU64_addr),
    ("bswap_and_clz_u64", bswapAndClzU64_addr),
    ("add128_u64", add128U64_addr),
    ("smaddl_sdiv_i64", smaddlSdivI64_addr),
    ("stack_spill_struct_update", stackSpillStructUpdate_addr)
  ]

theorem functionalCorrectnessLinkedProg_hasCodeBundle :
    functionalCorrectnessLinkedProg.hasCodeBundle functionalCorrectnessCodeBundle := by
  arm64_decide_code

theorem ite_beq_zero_udiv (a b : BitVec 64) :
    (if (b == 0#64) = true then 0#64 else a / b) = a / b := by
  by_cases h : b = 0#64 <;> simp [h]

theorem addWithCarry64_c_false (x y : BitVec 64) :
    (AddWithCarry64 x y false).snd.c = (x + y).ult x := by
  simp only [AddWithCarry64, Bool.false_eq_true, ↓reduceIte, BitVec.zero_add,
    BitVec.msb_eq_getLsbD_last]
  bv_bits

theorem divmodU64_ok (prog : Program)
    (h_code : DivModU64CodeAt prog) :
    prog.subroutineOk "divmod_u64" divmodU64Spec := by
  wp_init a s0
  wp_steps
  simp only [ite_beq_zero_udiv] at *
  wp_done

theorem divmodU64_prog_ok :
    divmodU64Prog.subroutineOk "divmod_u64" divmodU64Spec :=
  divmodU64_ok divmodU64Prog (by arm64_decide_code)

theorem divmodU64_ok_linked :
    functionalCorrectnessLinkedProg.subroutineOk "divmod_u64" divmodU64Spec :=
  divmodU64_ok functionalCorrectnessLinkedProg (by arm64_code_at functionalCorrectnessLinkedProg_hasCodeBundle)

theorem bswapAndClzU64_ok (prog : Program)
    (h_code : BswapAndClzU64CodeAt prog) :
    prog.subroutineOk "bswap_and_clz_u64" bswapAndClzU64Spec := by
  wp_init x s0
  wp_steps
  wp_done

theorem bswapAndClzU64_prog_ok :
    bswapAndClzU64Prog.subroutineOk "bswap_and_clz_u64" bswapAndClzU64Spec :=
  bswapAndClzU64_ok bswapAndClzU64Prog (by arm64_decide_code)

theorem bswapAndClzU64_ok_linked :
    functionalCorrectnessLinkedProg.subroutineOk "bswap_and_clz_u64" bswapAndClzU64Spec :=
  bswapAndClzU64_ok functionalCorrectnessLinkedProg (by arm64_code_at functionalCorrectnessLinkedProg_hasCodeBundle)

theorem add128U64_ok (prog : Program)
    (h_code : Add128U64CodeAt prog) :
    prog.subroutineOk "add128_u64" add128U64Spec := by
  wp_init a s0
  wp_steps
  simp only [addWithCarry64_c_false] at *
  wp_done

theorem add128U64_prog_ok :
    add128U64Prog.subroutineOk "add128_u64" add128U64Spec :=
  add128U64_ok add128U64Prog (by arm64_decide_code)

theorem add128U64_ok_linked :
    functionalCorrectnessLinkedProg.subroutineOk "add128_u64" add128U64Spec :=
  add128U64_ok functionalCorrectnessLinkedProg (by arm64_code_at functionalCorrectnessLinkedProg_hasCodeBundle)

theorem smaddlSdivI64_ok (prog : Program)
    (h_code : SmaddlSdivI64CodeAt prog) :
    prog.subroutineOk "smaddl_sdiv_i64" smaddlSdivI64Spec := by
  wp_init a s0
  wp_steps
  wp_done

theorem smaddlSdivI64_prog_ok :
    smaddlSdivI64Prog.subroutineOk "smaddl_sdiv_i64" smaddlSdivI64Spec :=
  smaddlSdivI64_ok smaddlSdivI64Prog (by arm64_decide_code)

theorem smaddlSdivI64_ok_linked :
    functionalCorrectnessLinkedProg.subroutineOk "smaddl_sdiv_i64" smaddlSdivI64Spec :=
  smaddlSdivI64_ok functionalCorrectnessLinkedProg (by arm64_code_at functionalCorrectnessLinkedProg_hasCodeBundle)

theorem stackSpillStructUpdate_ok (prog : Program)
    (h_code : StackSpillStructUpdateCodeAt prog) :
    prog.subroutineOk "stack_spill_struct_update" stackSpillStructUpdateSpec := by
  wp_init a s0
  wp_steps
  wp_done

theorem stackSpillStructUpdate_prog_ok :
    stackSpillStructUpdateProg.subroutineOk "stack_spill_struct_update" stackSpillStructUpdateSpec :=
  stackSpillStructUpdate_ok stackSpillStructUpdateProg (by arm64_decide_code)

theorem stackSpillStructUpdate_ok_linked :
    functionalCorrectnessLinkedProg.subroutineOk "stack_spill_struct_update" stackSpillStructUpdateSpec :=
  stackSpillStructUpdate_ok functionalCorrectnessLinkedProg (by arm64_code_at functionalCorrectnessLinkedProg_hasCodeBundle)

theorem functionalCorrectnessProofsChecked :
    (∀ prog, DivModU64CodeAt prog → prog.subroutineOk "divmod_u64" divmodU64Spec) ∧
    (∀ prog, BswapAndClzU64CodeAt prog → prog.subroutineOk "bswap_and_clz_u64" bswapAndClzU64Spec) ∧
    (∀ prog, Add128U64CodeAt prog → prog.subroutineOk "add128_u64" add128U64Spec) ∧
    (∀ prog, SmaddlSdivI64CodeAt prog → prog.subroutineOk "smaddl_sdiv_i64" smaddlSdivI64Spec) ∧
    (∀ prog, StackSpillStructUpdateCodeAt prog → prog.subroutineOk "stack_spill_struct_update" stackSpillStructUpdateSpec) ∧
    divmodU64Prog.subroutineOk "divmod_u64" divmodU64Spec ∧
    bswapAndClzU64Prog.subroutineOk "bswap_and_clz_u64" bswapAndClzU64Spec ∧
    add128U64Prog.subroutineOk "add128_u64" add128U64Spec ∧
    smaddlSdivI64Prog.subroutineOk "smaddl_sdiv_i64" smaddlSdivI64Spec ∧
    stackSpillStructUpdateProg.subroutineOk "stack_spill_struct_update" stackSpillStructUpdateSpec ∧
    functionalCorrectnessLinkedProg.subroutineOk "divmod_u64" divmodU64Spec ∧
    functionalCorrectnessLinkedProg.subroutineOk "bswap_and_clz_u64" bswapAndClzU64Spec ∧
    functionalCorrectnessLinkedProg.subroutineOk "add128_u64" add128U64Spec ∧
    functionalCorrectnessLinkedProg.subroutineOk "smaddl_sdiv_i64" smaddlSdivI64Spec ∧
    functionalCorrectnessLinkedProg.subroutineOk "stack_spill_struct_update" stackSpillStructUpdateSpec ∧
    functionalCorrectnessLinkedProg.hasCodeBundle functionalCorrectnessCodeBundle :=
  ⟨divmodU64_ok,
   bswapAndClzU64_ok,
   add128U64_ok,
   smaddlSdivI64_ok,
   stackSpillStructUpdate_ok,
   divmodU64_prog_ok,
   bswapAndClzU64_prog_ok,
   add128U64_prog_ok,
   smaddlSdivI64_prog_ok,
   stackSpillStructUpdate_prog_ok,
   divmodU64_ok_linked,
   bswapAndClzU64_ok_linked,
   add128U64_ok_linked,
   smaddlSdivI64_ok_linked,
   stackSpillStructUpdate_ok_linked,
   functionalCorrectnessLinkedProg_hasCodeBundle⟩

end Testing.FunctionalCorrectness
