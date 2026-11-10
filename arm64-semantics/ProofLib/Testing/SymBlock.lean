/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Testing.WpPerf
public import ProofLib.SepLogic.SymBlock.Tactic

/-!
# `sym_block` Regression Tests

Positive and negative (`#guard_msgs`) regression tests for `ProofLib.SepLogic.SymBlock`:
whole-block and prefix stepping, `SepWPp`, nested `∗` flattening, associative address matching,
narrow/128-bit/read-only cells, SIMD copies, condition flags, $O(1)$ fetch indexing, SP/PC
hypotheses, and loop back-edges.
-/

@[expose] public section

namespace Testing.SymBlock

open Arm64 ProofLib Testing.WpPerf

set_option maxHeartbeats 50000

theorem perf_60_steps_symblock_ok (b : BitVec 64) (H : String → Option (State → State))
    (h_code : (perfBaseProg.rebase b H).hasCode (b + 0x400#64) perf60StepsHex) :
    (perfBaseProg.rebase b H).subroutineOk "perf_60_steps" perf60StepsSpec := by
  wp_init a s0
  sym_block
  wp_done

theorem perf_60_steps_symblock_prefix_ok (b : BitVec 64) (H : String → Option (State → State))
    (h_code : (perfBaseProg.rebase b H).hasCode (b + 0x400#64) perf60StepsHex) :
    (perfBaseProg.rebase b H).subroutineOk "perf_60_steps" perf60StepsSpec := by
  wp_init a s0
  sym_block 3
  wp_sym_steps
  wp_done

-- Negative (`perf_60_steps_wrong_hint`): wrong branch hint at `cbz` is rejected.
/--
error: sym_block: could not discharge obligation 0#64 ≠ 0#64
-/
#guard_msgs (error, drop info) in
example (b : BitVec 64) (H : String → Option (State → State))
    (h_code : (perfBaseProg.rebase b H).hasCode (b + 0x400#64) perf60StepsHex) :
    (perfBaseProg.rebase b H).subroutineOk "perf_60_steps" perf60StepsSpec := by
  wp_init a s0
  sym_block (hints := "n")
  wp_done

-- Negative (`no_code_rejected`): goal whose first instruction cannot be fetched is rejected.
/--
error: sym_block: no instruction could be executed (no fetch at +0000000000000000)
-/
#guard_msgs (error, drop info) in
example (b : BitVec 64) (H : String → Option (State → State)) :
    (perfBaseProg.rebase b H).subroutineOk "perf_60_steps" perf60StepsSpec := by
  wp_init a s0
  sym_block

/-- Narrow-access fixture at offset `0x400`:
    `ldrb w1, [x0]; strb w1, [x0, #1]; ldr w2, [x0, #4]; str w2, [x0, #8]; adrp x3, 0; ret`. -/
def narrowProg : Program where
  base := 0#64
  code := []
  symbols := [("narrow", 0x400)]

@[simp, arm64_norm]
theorem narrowProg_fnOff : narrowProg.fnOff "narrow" = 0x400 := rfl

def narrowHex : List (BitVec 32) := "39400001 39000401 b9400402 b9000802 90000003 d65f03c0"

structure NarrowArgs where
  p : BitVec 64
  v : BitVec 8
  u : BitVec 8
  w : BitVec 32
  z : BitVec 32

abbrev narrowSpec : Spec NarrowArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.p⌝ ∗
    (a.p ↦₈ a.v) ∗ ((a.p + 1#64) ↦₈ a.u) ∗ ((a.p + 4#64) ↦₃₂ a.w) ∗ ((a.p + 8#64) ↦₃₂ a.z)
  post := fun a _ _ =>
    (a.p ↦₈ a.v) ∗ ((a.p + 1#64) ↦₈ a.v) ∗ ((a.p + 4#64) ↦₃₂ a.w) ∗ ((a.p + 8#64) ↦₃₂ a.w)

theorem narrow_symblock_ok (b : BitVec 64) (H : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (h_code : (narrowProg.rebase b H).hasCode (b + 0x400#64) narrowHex) :
    (narrowProg.rebase b H).subroutineOk "narrow" narrowSpec := by
  wp_init a s0
  sym_block
  wp_done

theorem narrow_symblock_resume_ok (b : BitVec 64) (H : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (h_code : (narrowProg.rebase b H).hasCode (b + 0x400#64) narrowHex) :
    (narrowProg.rebase b H).subroutineOk "narrow" narrowSpec := by
  wp_init a s0
  sym_block 2
  sym_block
  wp_done

/-! ## Panic-Aware `SepWPp` -/

section SepWPpTests

set_option maxHeartbeats 100000

abbrev sepwppSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨p, v⟩ s0 =>
    ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v)
  post := fun ⟨p, v⟩ _ sf =>
    ⌜sf.readReg64 .x0 = v + 1#64⌝ ∗ (p ↦₆₄ (v + 1#64))
  onPanic := fun _ _ _ => ⌜True⌝

theorem sepwpp_ret_symblock_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "sepwpp_fn" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x1 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf2 : prog.fetch (entry + 8#64) = some (.str .X64 .x1 (.Offset .x0 0#64)))
    (hf3 : prog.fetch (entry + 12#64) = some (.addSubImm .W64 .ADD .x0 .x1 0#12 false))
    (hf4 : prog.fetch (entry + 16#64) = some (.ret .lr)) :
    prog.subroutineOk "sepwpp_fn" sepwppSpec := by
  wpp_init a s0
  sym_block
  wp_done

end SepWPpTests

/-! ## Left-Nested `∗` Framing and Associative Stack-Offset Matching -/

section FramingAndAddrNormTests

set_option maxHeartbeats 100000

structure LeftNestedArgs where
  a : BitVec 64
  b : BitVec 64
  c : BitVec 64
  d : BitVec 64
  e : BitVec 64
  va : BitVec 64
  vb : BitVec 64
  vc : BitVec 64
  vd : BitVec 64
  ve : BitVec 64

abbrev leftNestedSpec : Spec LeftNestedArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.a ∧ s0.readReg64 .x1 = x.b ∧
     s0.readReg64 .x2 = x.c ∧ s0.readReg64 .x3 = x.d⌝ ∗
    ((((x.a ↦₆₄ x.va) ∗ (x.b ↦₆₄ x.vb)) ∗ (x.c ↦₆₄ x.vc)) ∗ (x.d ↦₆₄ x.vd)) ∗ (x.e ↦₆₄ x.ve)
  post := fun x _ sf =>
    ⌜sf.readReg64 .x4 = x.va + x.vc⌝ ∗
    (x.a ↦₆₄ x.va) ∗ (x.b ↦₆₄ (x.va + x.vc)) ∗ (x.c ↦₆₄ x.vc) ∗
    (x.d ↦₆₄ (x.va + x.vc)) ∗ (x.e ↦₆₄ x.ve)

theorem left_nested_sep_symblock_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "left_nested" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x4 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.ldr .W64 .X64 false .x5 (.Offset .x2 0#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.addSubShift .W64 .ADD .x4 .x4 .x5 .LSL 0))
    (hf3 : prog.fetch (entry + 12#64) = some (.str .X64 .x4 (.Offset .x1 0#64)))
    (hf4 : prog.fetch (entry + 16#64) = some (.str .X64 .x4 (.Offset .x3 0#64)))
    (hf5 : prog.fetch (entry + 20#64) = some (.ret .lr)) :
    prog.subroutineOk "left_nested" leftNestedSpec := by
  wp_init x s0
  sym_block
  wp_done

abbrev assocStackSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨v0, v1⟩ s0 =>
    ((s0.sp - 96#64 + 16#64) ↦₆₄ v0) ∗ ((s0.sp - 48#64) ↦₆₄ v1)
  post := fun ⟨_, v1⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = v1⌝ ∗
    ((s0.sp - 96#64 + 16#64) ↦₆₄ v1) ∗ ((s0.sp - 48#64) ↦₆₄ v1)

theorem assoc_stack_offset_symblock_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "assoc_stack" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.addSubImm .W64 .SUB .sp .sp 96#12 false))
    (hf1 : prog.fetch (entry + 4#64) = some (.ldr .W64 .X64 false .x0 (.Offset .sp 48#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.str .X64 .x0 (.Offset .sp 16#64)))
    (hf3 : prog.fetch (entry + 12#64) = some (.addSubImm .W64 .ADD .sp .sp 96#12 false))
    (hf4 : prog.fetch (entry + 16#64) = some (.ret .lr)) :
    prog.subroutineOk "assoc_stack" assocStackSpec := by
  wp_init x s0
  sym_block
  wp_done

end FramingAndAddrNormTests

/-! ## 16-Bit, 128-Bit, and Read-Only Cells -/

section WidthAndReadOnlyTests

set_option maxHeartbeats 100000

structure Narrow16ROArgs where
  p : BitVec 64
  ro : BitVec 64
  dst : BitVec 64
  h0 : BitVec 16
  h1 : BitVec 16
  q64 : BitVec 64
  q32 : BitVec 32
  q16 : BitVec 16
  q8 : BitVec 8
  q128 : BitVec 128
  d128 : BitVec 128

abbrev narrow16ROSpec : Spec Narrow16ROArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.p ∧ s0.readReg64 .x1 = x.ro ∧ s0.readReg64 .x2 = x.dst⌝ ∗
    (x.p ↦₁₆ x.h0) ∗ ((x.p + 2#64) ↦₁₆ x.h1) ∗
    (x.ro ↦₆₄ᵣ x.q64) ∗ ((x.ro + 8#64) ↦₃₂ᵣ x.q32) ∗
    ((x.ro + 12#64) ↦₁₆ᵣ x.q16) ∗ ((x.ro + 14#64) ↦₈ᵣ x.q8) ∗
    ((x.ro + 16#64) ↦₁₂₈ᵣ x.q128) ∗ (x.dst ↦₁₂₈ x.d128)
  post := fun x _ sf =>
    ⌜sf.readReg64 .x3 = x.q64 ∧
     sf.readReg64 .x4 = x.q32.zeroExtend 64 ∧
     sf.readReg64 .x5 = x.q16.zeroExtend 64 ∧
     sf.readReg64 .x6 = x.q8.zeroExtend 64 ∧
     sf.readVReg128 0#5 = x.q128⌝ ∗
    (x.p ↦₁₆ x.h0) ∗ ((x.p + 2#64) ↦₁₆ x.h0) ∗
    (x.ro ↦₆₄ᵣ x.q64) ∗ ((x.ro + 8#64) ↦₃₂ᵣ x.q32) ∗
    ((x.ro + 12#64) ↦₁₆ᵣ x.q16) ∗ ((x.ro + 14#64) ↦₈ᵣ x.q8) ∗
    ((x.ro + 16#64) ↦₁₂₈ᵣ x.q128) ∗ (x.dst ↦₁₂₈ x.q128)

theorem narrow16_and_readonly_symblock_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "narrow16_ro" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W32 .H16 false .x7 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.str .H16 .x7 (.Offset .x0 2#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ldr .W64 .X64 false .x3 (.Offset .x1 0#64)))
    (hf3 : prog.fetch (entry + 12#64) = some (.ldr .W32 .W32 false .x4 (.Offset .x1 8#64)))
    (hf4 : prog.fetch (entry + 16#64) = some (.ldr .W32 .H16 false .x5 (.Offset .x1 12#64)))
    (hf5 : prog.fetch (entry + 20#64) = some (.ldr .W32 .B8 false .x6 (.Offset .x1 14#64)))
    (hf6 : prog.fetch (entry + 24#64) = some (.ldrSimd .Q128 0#5 (.Offset .x1 16#64)))
    (hf7 : prog.fetch (entry + 28#64) = some (.strSimd .Q128 0#5 (.Offset .x2 0#64)))
    (hf8 : prog.fetch (entry + 32#64) = some (.ret .lr)) :
    prog.subroutineOk "narrow16_ro" narrow16ROSpec := by
  wp_init x s0
  sym_block
  wp_done

abbrev storeROSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨p, v⟩ s0 => ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ᵣ v)
  post := fun ⟨p, v⟩ _ _ => p ↦₆₄ᵣ v

-- Negative (`store_readonly_rejected`): storing to a `↦ᵣ` cell is rejected.
/--
error: sym_block: no instruction could be executed (cannot store to read-only cell at +0000000000000000)
-/
#guard_msgs (error, drop info) in
example (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "store_ro" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.str .X64 .x1 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.ret .lr)) :
    prog.subroutineOk "store_ro" storeROSpec := by
  wp_init a s0
  sym_block

end WidthAndReadOnlyTests

/-! ## 128-Bit SIMD Struct Copies -/

section SimdStructCopyTests

set_option maxHeartbeats 120000

structure SimdCopy128Args where
  src : BitVec 64
  dst : BitVec 64
  s0 : BitVec 128
  s1 : BitVec 128
  s2 : BitVec 128
  d0 : BitVec 128
  d1 : BitVec 128
  d2 : BitVec 128

abbrev simdCopy128Spec : Spec SimdCopy128Args where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.src ∧ s0.readReg64 .x1 = x.dst⌝ ∗
    (x.src ↦₁₂₈ x.s0) ∗ ((x.src + 16#64) ↦₁₂₈ x.s1) ∗ ((x.src + 32#64) ↦₁₂₈ x.s2) ∗
    (x.dst ↦₁₂₈ x.d0) ∗ ((x.dst + 16#64) ↦₁₂₈ x.d1) ∗ ((x.dst + 32#64) ↦₁₂₈ x.d2)
  post := fun x _ _ =>
    (x.src ↦₁₂₈ x.s0) ∗ ((x.src + 16#64) ↦₁₂₈ x.s1) ∗ ((x.src + 32#64) ↦₁₂₈ x.s2) ∗
    (x.dst ↦₁₂₈ x.s0) ∗ ((x.dst + 16#64) ↦₁₂₈ x.s1) ∗ ((x.dst + 32#64) ↦₁₂₈ x.s2)

theorem simd_q_struct_copy_128_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "simd_copy_128" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldrSimd .Q128 0#5 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.strSimd .Q128 0#5 (.Offset .x1 0#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ldpSimd .Q128 1#5 2#5 (.Offset .x0 16#64)))
    (hf3 : prog.fetch (entry + 12#64) = some (.stpSimd .Q128 1#5 2#5 (.Offset .x1 16#64)))
    (hf4 : prog.fetch (entry + 16#64) = some (.ret .lr)) :
    prog.subroutineOk "simd_copy_128" simdCopy128Spec := by
  wp_init x s0
  sym_block
  wp_done

structure SimdCopy64Args where
  src : BitVec 64
  dst : BitVec 64
  s0 : BitVec 64
  s1 : BitVec 64
  s2 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64
  d0 : BitVec 64
  d1 : BitVec 64
  d2 : BitVec 64
  d3 : BitVec 64
  d4 : BitVec 64
  d5 : BitVec 64

abbrev simdCopy64Spec : Spec SimdCopy64Args where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.src ∧ s0.readReg64 .x1 = x.dst⌝ ∗
    (x.src ↦₆₄ x.s0) ∗ ((x.src + 8#64) ↦₆₄ x.s1) ∗
    ((x.src + 16#64) ↦₆₄ x.s2) ∗ ((x.src + 24#64) ↦₆₄ x.s3) ∗
    ((x.src + 32#64) ↦₆₄ x.s4) ∗ ((x.src + 40#64) ↦₆₄ x.s5) ∗
    (x.dst ↦₆₄ x.d0) ∗ ((x.dst + 8#64) ↦₆₄ x.d1) ∗
    ((x.dst + 16#64) ↦₆₄ x.d2) ∗ ((x.dst + 24#64) ↦₆₄ x.d3) ∗
    ((x.dst + 32#64) ↦₆₄ x.d4) ∗ ((x.dst + 40#64) ↦₆₄ x.d5)
  post := fun x _ _ =>
    (x.src ↦₆₄ x.s0) ∗ ((x.src + 8#64) ↦₆₄ x.s1) ∗
    ((x.src + 16#64) ↦₆₄ x.s2) ∗ ((x.src + 24#64) ↦₆₄ x.s3) ∗
    ((x.src + 32#64) ↦₆₄ x.s4) ∗ ((x.src + 40#64) ↦₆₄ x.s5) ∗
    (x.dst ↦₆₄ x.s0) ∗ ((x.dst + 8#64) ↦₆₄ x.s1) ∗
    ((x.dst + 16#64) ↦₆₄ x.s2) ∗ ((x.dst + 24#64) ↦₆₄ x.s3) ∗
    ((x.dst + 32#64) ↦₆₄ x.s4) ∗ ((x.dst + 40#64) ↦₆₄ x.s5)

theorem simd_q_struct_copy_64_pairs_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "simd_copy_64" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldrSimd .Q128 0#5 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.strSimd .Q128 0#5 (.Offset .x1 0#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ldpSimd .Q128 1#5 2#5 (.Offset .x0 16#64)))
    (hf3 : prog.fetch (entry + 12#64) = some (.stpSimd .Q128 1#5 2#5 (.Offset .x1 16#64)))
    (hf4 : prog.fetch (entry + 16#64) = some (.ret .lr)) :
    prog.subroutineOk "simd_copy_64" simdCopy64Spec := by
  wp_init x s0
  sym_block
  wp_done

end SimdStructCopyTests

/-! ## Flag Conditions -/

section FlagCondTests

set_option maxHeartbeats 120000

abbrev cmnAddsSpec : Spec (BitVec 64) where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = 0xffffffffffffffff#64 ∧
     s0.readReg64 .x1 = x ∧
     BitVec.saddOverflow x 1#64 = false ∧
     BitVec.uaddOverflow (x.truncate 32) 1#32 = false⌝
  post := fun x _ sf =>
    ⌜sf.readReg64 .x2 = x + 1#64 ∧ sf.readReg64 .x4 = 4#64⌝

theorem flags_cmn_and_adds_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "cmn_adds" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.moveWide .W64 .MOVZ .x4 0#16 0))
    (hf1 : prog.fetch (entry + 4#64) = some (.addSubImm .W64 .ADDS .xzr .x0 1#12 false))
    (hf2 : prog.fetch (entry + 8#64) = some (.bCond .EQ 8#64))
    (_hf3 : prog.fetch (entry + 12#64) = some (.moveWide .W64 .MOVZ .x4 99#16 0))
    (hf4 : prog.fetch (entry + 16#64) = some (.addSubImm .W64 .ADD .x4 .x4 1#12 false))
    (hf5 : prog.fetch (entry + 20#64) = some (.addSubImm .W64 .ADDS .xzr .x0 4095#12 false))
    (hf6 : prog.fetch (entry + 24#64) = some (.bCond .HI 8#64))
    (_hf7 : prog.fetch (entry + 28#64) = some (.moveWide .W64 .MOVZ .x4 99#16 0))
    (hf8 : prog.fetch (entry + 32#64) = some (.addSubImm .W64 .ADD .x4 .x4 1#12 false))
    (hf9 : prog.fetch (entry + 36#64) = some (.addSubImm .W64 .ADDS .x2 .x1 1#12 false))
    (hf10 : prog.fetch (entry + 40#64) = some (.bCond .VC 8#64))
    (_hf11 : prog.fetch (entry + 44#64) = some (.moveWide .W64 .MOVZ .x4 99#16 0))
    (hf12 : prog.fetch (entry + 48#64) = some (.addSubImm .W64 .ADD .x4 .x4 1#12 false))
    (hf13 : prog.fetch (entry + 52#64) = some (.addSubImm .W32 .ADDS .x3 .x1 1#12 false))
    (hf14 : prog.fetch (entry + 56#64) = some (.bCond .CC 8#64))
    (_hf15 : prog.fetch (entry + 60#64) = some (.moveWide .W64 .MOVZ .x4 99#16 0))
    (hf16 : prog.fetch (entry + 64#64) = some (.addSubImm .W64 .ADD .x4 .x4 1#12 false))
    (hf17 : prog.fetch (entry + 68#64) = some (.ret .lr)) :
    prog.subroutineOk "cmn_adds" cmnAddsSpec := by
  wp_init x s0
  sym_block
  wp_done

abbrev w32SignedCondSpec : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg64 .x0 = 5#64 ∧ s0.readReg64 .x1 = 10#64⌝
  post := fun _ _ sf =>
    ⌜sf.readReg64 .x2 = 2#64⌝

theorem flags_w32_and_signed_conds_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "w32_signed" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.moveWide .W64 .MOVZ .x2 0#16 0))
    (hf1 : prog.fetch (entry + 4#64) = some (.addSubShift .W32 .SUBS .xzr .x0 .x1 .LSL 0))
    (hf2 : prog.fetch (entry + 8#64) = some (.bCond .LT 8#64))
    (_hf3 : prog.fetch (entry + 12#64) = some (.moveWide .W64 .MOVZ .x2 99#16 0))
    (hf4 : prog.fetch (entry + 16#64) = some (.bCond .GE 8#64))
    (hf5 : prog.fetch (entry + 20#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf6 : prog.fetch (entry + 24#64) = some (.addSubShift .W64 .SUBS .xzr .x0 .x1 .LSL 0))
    (hf7 : prog.fetch (entry + 28#64) = some (.bCond .LE 8#64))
    (_hf8 : prog.fetch (entry + 32#64) = some (.moveWide .W64 .MOVZ .x2 99#16 0))
    (hf9 : prog.fetch (entry + 36#64) = some (.bCond .GT 8#64))
    (hf10 : prog.fetch (entry + 40#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf11 : prog.fetch (entry + 44#64) = some (.bCond .LS 8#64))
    (_hf12 : prog.fetch (entry + 48#64) = some (.moveWide .W64 .MOVZ .x2 99#16 0))
    (hf13 : prog.fetch (entry + 52#64) = some (.bCond .AL 8#64))
    (_hf14 : prog.fetch (entry + 56#64) = some (.moveWide .W64 .MOVZ .x2 99#16 0))
    (hf15 : prog.fetch (entry + 60#64) = some (.bCond .NV 8#64))
    (_hf16 : prog.fetch (entry + 64#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf17 : prog.fetch (entry + 68#64) = some (.ret .lr)) :
    prog.subroutineOk "w32_signed" w32SignedCondSpec := by
  wp_init u s0
  sym_block
  wp_done

abbrev tstAndsBicsSpec : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg64 .x0 = 0x100#64 ∧ s0.readReg64 .x1 = 0x0f0#64⌝
  post := fun _ _ sf =>
    ⌜sf.readReg64 .x4 = 3#64⌝

theorem flags_tst_ands_bics_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "tst_ands_bics" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.moveWide .W64 .MOVZ .x4 0#16 0))
    (hf1 : prog.fetch (entry + 4#64) = some (.logicalImm .W64 .ANDS .xzr .x0 0xff#64))
    (hf2 : prog.fetch (entry + 8#64) = some (.bCond .EQ 8#64))
    (_hf3 : prog.fetch (entry + 12#64) = some (.moveWide .W64 .MOVZ .x4 99#16 0))
    (hf4 : prog.fetch (entry + 16#64) = some (.addSubImm .W64 .ADD .x4 .x4 1#12 false))
    (hf5 : prog.fetch (entry + 20#64) = some (.logicalShift .W32 .ANDS .x2 .x0 .x1 .LSL 0))
    (hf6 : prog.fetch (entry + 24#64) = some (.bCond .PL 8#64))
    (_hf7 : prog.fetch (entry + 28#64) = some (.moveWide .W64 .MOVZ .x4 99#16 0))
    (hf8 : prog.fetch (entry + 32#64) = some (.addSubImm .W64 .ADD .x4 .x4 1#12 false))
    (hf9 : prog.fetch (entry + 36#64) = some (.logicalShift .W64 .BICS .x3 .x0 .x1 .LSL 0))
    (hf10 : prog.fetch (entry + 40#64) = some (.bCond .NE 8#64))
    (_hf11 : prog.fetch (entry + 44#64) = some (.moveWide .W64 .MOVZ .x4 99#16 0))
    (hf12 : prog.fetch (entry + 48#64) = some (.addSubImm .W64 .ADD .x4 .x4 1#12 false))
    (hf13 : prog.fetch (entry + 52#64) = some (.ret .lr)) :
    prog.subroutineOk "tst_ands_bics" tstAndsBicsSpec := by
  wp_init u s0
  sym_block
  wp_done

end FlagCondTests

/-! ## Expanded Scalar and Addressing Instructions -/

section ExpandedScalarTests

set_option maxHeartbeats 150000

structure ScalarMemArgs where
  p : BitVec 64
  q : BitVec 64
  w0 : BitVec 32
  w1 : BitVec 32
  sw0 : BitVec 32
  sw1 : BitVec 32
  sb0 : BitVec 8
  sh0 : BitVec 16
  d0 : BitVec 32
  d1 : BitVec 32

abbrev scalarMovkMemSpec : Spec ScalarMemArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x3 = x.p ∧ s0.readReg64 .x4 = x.q⌝ ∗
    (x.p ↦₃₂ x.w0) ∗ ((x.p + 4#64) ↦₃₂ x.w1) ∗
    ((x.p + 8#64) ↦₃₂ x.sw0) ∗ ((x.p + 12#64) ↦₃₂ x.sw1) ∗
    ((x.p + 16#64) ↦₈ x.sb0) ∗ ((x.p + 18#64) ↦₁₆ x.sh0) ∗
    (x.q ↦₃₂ x.d0) ∗ ((x.q + 4#64) ↦₃₂ x.d1)
  post := fun x _ sf =>
    ⌜sf.readReg64 .x0 = 0x1111222233334444#64 ∧
     sf.readReg64 .x1 = x.w0.zeroExtend 64 ∧
     sf.readReg64 .x2 = x.w1.zeroExtend 64 ∧
     sf.readReg64 .x5 = x.sw0.signExtend 64 ∧
     sf.readReg64 .x6 = x.sw1.signExtend 64 ∧
     sf.readReg64 .x7 = x.sw0.signExtend 64 ∧
     sf.readReg64 .x8 = x.sb0.signExtend 64 ∧
     sf.readReg64 .x9 = x.sh0.signExtend 64⌝ ∗
    (x.p ↦₃₂ x.w0) ∗ ((x.p + 4#64) ↦₃₂ x.w1) ∗
    ((x.p + 8#64) ↦₃₂ x.sw0) ∗ ((x.p + 12#64) ↦₃₂ x.sw1) ∗
    ((x.p + 16#64) ↦₈ x.sb0) ∗ ((x.p + 18#64) ↦₁₆ x.sh0) ∗
    (x.q ↦₃₂ x.w0) ∗ ((x.q + 4#64) ↦₃₂ x.w1)

theorem scalar_movk_ldp32_ldpsw_sext_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "scalar_movk_mem" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.moveWide .W64 .MOVZ .x0 0x4444#16 0))
    (hf1 : prog.fetch (entry + 4#64) = some (.moveWide .W64 .MOVK .x0 0x3333#16 16))
    (hf2 : prog.fetch (entry + 8#64) = some (.moveWide .W64 .MOVK .x0 0x2222#16 32))
    (hf3 : prog.fetch (entry + 12#64) = some (.moveWide .W64 .MOVK .x0 0x1111#16 48))
    (hf4 : prog.fetch (entry + 16#64) = some (.ldp .W32 false .x1 .x2 (.Offset .x3 0#64)))
    (hf5 : prog.fetch (entry + 20#64) = some (.stp .W32 .x1 .x2 (.Offset .x4 0#64)))
    (hf6 : prog.fetch (entry + 24#64) = some (.ldp .W64 true .x5 .x6 (.Offset .x3 8#64)))
    (hf7 : prog.fetch (entry + 28#64) = some (.ldr .W64 .W32 true .x7 (.Offset .x3 8#64)))
    (hf8 : prog.fetch (entry + 32#64) = some (.ldr .W64 .B8 true .x8 (.Offset .x3 16#64)))
    (hf9 : prog.fetch (entry + 36#64) = some (.ldr .W64 .H16 true .x9 (.Offset .x3 18#64)))
    (hf10 : prog.fetch (entry + 40#64) = some (.ret .lr)) :
    prog.subroutineOk "scalar_movk_mem" scalarMovkMemSpec := by
  wp_init x s0
  sym_block
  wp_done

structure ScalarAluSysArgs where
  src : BitVec 64
  dst : BitVec 64
  v : BitVec 64
  oldDst : BitVec 64
  newTp : BitVec 64

abbrev scalarAluSysSpec : Spec ScalarAluSysArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = 2#64 ∧
     s0.readReg64 .x1 = 3#64 ∧
     s0.readReg64 .x3 = x.src ∧
     s0.readReg64 .x4 = x.dst ∧
     s0.readReg64 .x18 = x.newTp⌝ ∗
    ((x.src + 24#64) ↦₆₄ x.v) ∗ ((x.dst + 12#64) ↦₆₄ x.oldDst)
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x2 = x.dst ∧
     sf.readReg64 .x5 = x.src ∧
     sf.readReg64 .x6 = ~~~x.dst ∧
     sf.readReg64 .x7 = -x.dst ∧
     sf.readReg64 .x8 = x.src + 24#64 ∧
     sf.readReg64 .x9 = x.src - 12#64 ∧
     sf.readReg64 .x10 = reverseBits x.src ∧
     sf.readReg64 .x11 = rev64 x.src ∧
     sf.readReg64 .x12 = BitVec.ofNat 64 (countLeadingZeros x.src) ∧
     sf.readReg64 .x13 = ((BitVec.ofNat 64 (countLeadingSigns (x.src.truncate 32))).truncate 32).zeroExtend 64 ∧
     sf.readReg64 .x14 = x.src + 6#64 ∧
     sf.readReg64 .x15 = x.src - 6#64 ∧
     sf.readReg64 .x16 = x.src + 6#64 ∧
     sf.readReg64 .x17 = 0#64 ∧
     sf.readReg64 .x18 = s0.pc + 0x6c#64 ∧
     sf.readReg64 .x0 = x.v ∧
     sf.readReg64 .x4 = s0.tpidrEl0 ∧
     sf.readReg64 .x3 = x.newTp ∧
     sf.readReg64 .x1 = 4#64⌝ ∗
    ((x.src + 24#64) ↦₆₄ x.v) ∗ ((x.dst + 12#64) ↦₆₄ x.v)

theorem scalar_tbz_csel_ext_dp1_dp3_adr_sysreg_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "scalar_alu_sys" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.tbz .W64 false .x0 3 8#64))
    (_hf1 : prog.fetch (entry + 4#64) = some (.moveWide .W64 .MOVZ .x0 99#16 0))
    (hf2 : prog.fetch (entry + 8#64) = some (.tbz .W32 true .x0 1 8#64))
    (_hf3 : prog.fetch (entry + 12#64) = some (.moveWide .W64 .MOVZ .x0 99#16 0))
    (hf4 : prog.fetch (entry + 16#64) = some (.addSubShift .W64 .SUBS .xzr .x0 .x1 .LSL 0))
    (hf5 : prog.fetch (entry + 20#64) = some (.condSelect .W64 .CSEL .x2 .x3 .x4 .EQ))
    (hf6 : prog.fetch (entry + 24#64) = some (.condSelect .W64 .CSINC .x5 .x3 .x4 .NE))
    (hf7 : prog.fetch (entry + 28#64) = some (.condSelect .W64 .CSINV .x6 .x3 .x4 .EQ))
    (hf8 : prog.fetch (entry + 32#64) = some (.condSelect .W64 .CSNEG .x7 .x3 .x4 .EQ))
    (hf9 : prog.fetch (entry + 36#64) = some (.addSubExt .W64 .ADD .x8 .x3 .x1 .UXTW 3))
    (hf10 : prog.fetch (entry + 40#64) = some (.addSubExt .W64 .SUB .x9 .x3 .x1 .SXTW 2))
    (hf11 : prog.fetch (entry + 44#64) = some (.dataProc1 .W64 .RBIT .x10 .x3))
    (hf12 : prog.fetch (entry + 48#64) = some (.dataProc1 .W64 .REV .x11 .x3))
    (hf13 : prog.fetch (entry + 52#64) = some (.dataProc1 .W64 .CLZ .x12 .x3))
    (hf14 : prog.fetch (entry + 56#64) = some (.dataProc1 .W32 .CLS .x13 .x3))
    (hf15 : prog.fetch (entry + 60#64) = some (.dataProc3 .W64 .MADD .x14 .x0 .x1 .x3))
    (hf16 : prog.fetch (entry + 64#64) = some (.dataProc3 .W64 .MSUB .x15 .x0 .x1 .x3))
    (hf17 : prog.fetch (entry + 68#64) = some (.dataProc3 .W64 .SMADDL .x16 .x0 .x1 .x3))
    (hf18 : prog.fetch (entry + 72#64) = some (.dataProc3 .W64 .UMULH .x17 .x0 .x1 .xzr))
    (hf19 : prog.fetch (entry + 76#64) = some (.ldr .W64 .X64 false .x0 (.RegOffset .x3 .x1 .UXTW 3)))
    (hf20 : prog.fetch (entry + 80#64) = some (.str .X64 .x0 (.RegOffset .x4 .x1 .UXTW 2)))
    (hf21 : prog.fetch (entry + 84#64) = some (.sysReg true 0x5e82#15 .x4))
    (hf22 : prog.fetch (entry + 88#64) = some (.sysReg false 0x5e82#15 .x18))
    (hf23 : prog.fetch (entry + 92#64) = some (.adr false .x18 0x10#64))
    (hf24 : prog.fetch (entry + 96#64) = some .nop)
    (hf25 : prog.fetch (entry + 100#64) = some (.hint 1#7))
    (hf26 : prog.fetch (entry + 104#64) = some (.barrier 0xb#4 5#3))
    (hf27 : prog.fetch (entry + 108#64) = some (.prfm 0#5 (.Offset .x3 0#64)))
    (hf28 : prog.fetch (entry + 112#64) = some (.prfmLit 0#5 0#64))
    (hf29 : prog.fetch (entry + 116#64) = some (.sysReg true 0x5e82#15 .x3))
    (hf30 : prog.fetch (entry + 120#64) = some (.sysReg false 0x5e82#15 .x4))
    (hf31 : prog.fetch (entry + 124#64) = some (.sysReg true 0x5807#15 .x1))
    (hf32 : prog.fetch (entry + 128#64) = some (.ret .lr)) :
    prog.subroutineOk "scalar_alu_sys" scalarAluSysSpec := by
  wp_init x s0
  sym_block
  wp_done

end ExpandedScalarTests

/-! ## Pre-Indexed `Program.fetch` Lookup -/

section LargeFetchIndexTests

set_option maxHeartbeats 100000

abbrev large30Spec : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨p, v⟩ s0 =>
    ⌜s0.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v) ∗ ((p + 8#64) ↦₆₄ 0#64)
  post := fun ⟨p, v⟩ _ sf =>
    ⌜sf.readReg64 .x0 = v + 22#64⌝ ∗ (p ↦₆₄ v) ∗ ((p + 8#64) ↦₆₄ (v + 22#64))

theorem large_30_insn_fetch_index_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "large_30" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x1 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf2 : prog.fetch (entry + 8#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf3 : prog.fetch (entry + 12#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf4 : prog.fetch (entry + 16#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf5 : prog.fetch (entry + 20#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf6 : prog.fetch (entry + 24#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf7 : prog.fetch (entry + 28#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf8 : prog.fetch (entry + 32#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf9 : prog.fetch (entry + 36#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf10 : prog.fetch (entry + 40#64) = some (.addSubImm .W64 .ADD .x1 .x1 1#12 false))
    (hf11 : prog.fetch (entry + 44#64) = some (.str .X64 .x1 (.Offset .x0 8#64)))
    (hf12 : prog.fetch (entry + 48#64) = some (.ldr .W64 .X64 false .x2 (.Offset .x0 8#64)))
    (hf13 : prog.fetch (entry + 52#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf14 : prog.fetch (entry + 56#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf15 : prog.fetch (entry + 60#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf16 : prog.fetch (entry + 64#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf17 : prog.fetch (entry + 68#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf18 : prog.fetch (entry + 72#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf19 : prog.fetch (entry + 76#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf20 : prog.fetch (entry + 80#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf21 : prog.fetch (entry + 84#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf22 : prog.fetch (entry + 88#64) = some (.addSubImm .W64 .ADD .x2 .x2 1#12 false))
    (hf23 : prog.fetch (entry + 92#64) = some (.str .X64 .x2 (.Offset .x0 8#64)))
    (hf24 : prog.fetch (entry + 96#64) = some (.ldr .W64 .X64 false .x3 (.Offset .x0 8#64)))
    (hf25 : prog.fetch (entry + 100#64) = some (.addSubImm .W64 .ADD .x3 .x3 1#12 false))
    (hf26 : prog.fetch (entry + 104#64) = some (.addSubImm .W64 .ADD .x3 .x3 1#12 false))
    (hf27 : prog.fetch (entry + 108#64) = some (.str .X64 .x3 (.Offset .x0 8#64)))
    (hf28 : prog.fetch (entry + 112#64) = some (.addSubImm .W64 .ADD .x0 .x3 0#12 false))
    (hf29 : prog.fetch (entry + 116#64) = some (.ret .lr)) :
    prog.subroutineOk "large_30" large30Spec := by
  wp_init x s0
  sym_block
  wp_done

end LargeFetchIndexTests

/-! ## Idempotency at `targetPC` -/

theorem sym_block_idempotent_at_target (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "idemp" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.addSubImm .W64 .ADD .x0 .x0 1#12 false))
    (hf1 : prog.fetch (entry + 4#64) = some (.ret .lr)) :
    prog.subroutineOk "idemp"
      { pre := fun (x : BitVec 64) s0 => ⌜s0.readReg64 .x0 = x⌝
        post := fun x _ sf => ⌜sf.readReg64 .x0 = x + 1#64⌝ } := by
  wp_init x s0
  sym_block
  sym_block
  wp_done

/-! ## Narrow Load/Store Round-Trip Simplification -/

section NarrowRoundTripTests

structure NarrowRoundTripArgs where
  src : BitVec 64
  dst : BitVec 64
  v16 : BitVec 16
  v8 : BitVec 8
  v32 : BitVec 32
  d16 : BitVec 16
  d8 : BitVec 8
  d32 : BitVec 32

abbrev narrowRoundTripSpec : Spec NarrowRoundTripArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.src ∧ s0.readReg64 .x1 = x.dst⌝ ∗
    (x.src ↦₁₆ x.v16) ∗ ((x.src + 2#64) ↦₈ x.v8) ∗ ((x.src + 4#64) ↦₃₂ x.v32) ∗
    (x.dst ↦₁₆ x.d16) ∗ ((x.dst + 2#64) ↦₈ x.d8) ∗ ((x.dst + 4#64) ↦₃₂ x.d32)
  post := fun x _ _ =>
    (x.src ↦₁₆ x.v16) ∗ ((x.src + 2#64) ↦₈ x.v8) ∗ ((x.src + 4#64) ↦₃₂ x.v32) ∗
    (x.dst ↦₁₆ x.v16) ∗ ((x.dst + 2#64) ↦₈ x.v8) ∗ ((x.dst + 4#64) ↦₃₂ x.v32)

private theorem exact_cell16 (p : BitVec 64) (v : BitVec 16) : (p ↦₁₆ v) = (p ↦₁₆ v) := rfl
private theorem exact_cell8 (p : BitVec 64) (v : BitVec 8) : (p ↦₈ v) = (p ↦₈ v) := rfl
private theorem exact_cell32 (p : BitVec 64) (v : BitVec 32) : (p ↦₃₂ v) = (p ↦₃₂ v) := rfl

theorem narrow_roundtrip_mktrunc_ok (prog : Program) (entry : BitVec 64)
    (h_off : prog.fnAddr "narrow_roundtrip" = entry)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W32 .H16 false .x2 (.Offset .x0 0#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.str .H16 .x2 (.Offset .x1 0#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ldr .W32 .B8 false .x3 (.Offset .x0 2#64)))
    (hf3 : prog.fetch (entry + 12#64) = some (.str .B8 .x3 (.Offset .x1 2#64)))
    (hf4 : prog.fetch (entry + 16#64) = some (.ldr .W32 .W32 false .x4 (.Offset .x0 4#64)))
    (hf5 : prog.fetch (entry + 20#64) = some (.str .W32 .x4 (.Offset .x1 4#64)))
    (hf6 : prog.fetch (entry + 24#64) = some (.ret .lr)) :
    prog.subroutineOk "narrow_roundtrip" narrowRoundTripSpec := by
  wp_init x s0
  sym_block
  wp_conv_pre =>
    rw [exact_cell16 x.dst x.v16, exact_cell8 (x.dst + 2#64) x.v8, exact_cell32 (x.dst + 4#64) x.v32]
  wp_done

end NarrowRoundTripTests

/-! ## Stack-Pointer Equality Hypotheses -/

section SpHypothesisTests

set_option maxHeartbeats 100000

theorem sp_hyp_direct_sepwp_ok (prog : Program) (entry baseSp v0 v1 : BitVec 64) (st : State)
    (hrun : st.status = .Running)
    (hpc : st.pc = entry + 0#64)
    (hsp : st.sp = baseSp - 96#64)
    (halign : baseSp &&& 0xf#64 = 0#64)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x0 (.Offset .sp 16#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.str .X64 .x0 (.Offset .sp 32#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ret .lr)) :
    SepWP prog (st.readReg64 .lr) st
      (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v1))
      (sepPost (fun sf => sf.readReg64 .x0 = v0 ∧ st.sp = baseSp - 96#64)
        (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v0))) := by
  sym_block
  have _ := hsp
  wp_done

theorem sp_readreg64_conjunct_sepwp_ok (prog : Program) (entry baseSp arg v0 v1 : BitVec 64)
    (st : State)
    (hinv : st.readReg64 .x1 = arg ∧ st.readReg64 .sp = baseSp - 96#64 ∧ st.status = .Running)
    (hpc : st.pc = entry + 0#64)
    (halign : baseSp &&& 0xf#64 = 0#64)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x0 (.Offset .sp 16#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.str .X64 .x0 (.Offset .sp 32#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ret .lr)) :
    SepWP prog (st.readReg64 .lr) st
      (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v1))
      (sepPost (fun sf => sf.readReg64 .x0 = v0 ∧ sf.readReg64 .x1 = arg)
        (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v0))) := by
  sym_block
  have _ := hinv
  wp_done

theorem sp_hyp_spine_no_sp_write_ok (prog : Program) (entry baseSp v0 v1 : BitVec 64) (s0 : State)
    (hrun : s0.status = .Running)
    (hpc : s0.pc = entry + 0#64)
    (hsp : s0.sp = baseSp - 96#64)
    (halign : baseSp &&& 0xf#64 = 0#64)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x0 (.Offset .sp 16#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.str .X64 .x0 (.Offset .sp 32#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ret .lr)) :
    SepWP prog (s0.readReg64 .lr) (s0.writeReg64 (.gpr 2#5) 7#64)
      (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v1))
      (sepPost (fun sf => sf.readReg64 .x0 = v0 ∧ sf.readReg64 .x2 = 7#64)
        (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v0))) := by
  sym_block
  have _ := hsp
  wp_done

theorem sp_hyp_sepwpp_ok (prog : Program) (entry baseSp v0 v1 : BitVec 64) (st : State)
    (hinv : st.readReg64 .sp = baseSp - 96#64 ∧ st.status = .Running)
    (hpc : st.pc = entry + 0#64)
    (halign : (baseSp &&& 15#64 == 0#64) = true)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x0 (.Offset .sp 16#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.str .X64 .x0 (.Offset .sp 32#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ret .lr)) :
    SepWPp prog (st.readReg64 .lr) st
      (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v1))
      (sepPost (fun sf => sf.readReg64 .x0 = v0)
        (((baseSp - 80#64) ↦₆₄ v0) ∗ ((baseSp - 64#64) ↦₆₄ v0)))
      (fun _ _ => True) := by
  sym_block
  have _ := hinv
  wp_done

abbrev testFrameOff : BitVec 64 := 64#64 + 32#64

theorem sp_hyp_spaligned_and_abbrev_frame_ok (prog : Program) (entry v0 v1 : BitVec 64)
    (s0 st : State)
    (hrun : st.status = .Running)
    (hpc : st.pc = entry + 0#64)
    (hsp : st.sp = s0.sp - testFrameOff)
    (halign : s0.spAligned = true)
    (hf0 : prog.fetch (entry + 0#64) = some (.ldr .W64 .X64 false .x0 (.Offset .sp 16#64)))
    (hf1 : prog.fetch (entry + 4#64) = some (.str .X64 .x0 (.Offset .sp 32#64)))
    (hf2 : prog.fetch (entry + 8#64) = some (.ret .lr)) :
    SepWP prog (st.readReg64 .lr) st
      (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 64#64) ↦₆₄ v1))
      (sepPost (fun sf => sf.readReg64 .x0 = v0)
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 64#64) ↦₆₄ v0))) := by
  sym_block
  have _ := hsp
  wp_done

end SpHypothesisTests

/-! ## Named Offset `abbrev`s in PCs and Fetches -/

section NamedOffsetAbbrevTests

set_option maxHeartbeats 100000

abbrev testLoopOff : BitVec 64 := 8#64 + 8#64
abbrev testNextOff : BitVec 64 := 20#64
abbrev testLargeOff : BitVec 64 := 0x100000000#64 + 0x200000000#64

theorem named_offset_abbrev_hpc_ok (prog : Program) (entry x : BitVec 64) (st : State)
    (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = x)
    (hpc : st.pc = entry + testLoopOff)
    (hf0 : prog.fetch (entry + 16#64) = some (.addSubImm .W64 .ADD .x0 .x0 1#12 false))
    (hf1 : prog.fetch (entry + 20#64) = some (.ret .lr)) :
    SepWP prog (st.readReg64 .lr) st emp
      (sepPost (fun sf => sf.readReg64 .x0 = x + 1#64) emp) := by
  sym_block
  wp_done

theorem named_offset_abbrev_fetch_and_target_ok (prog : Program) (entry x : BitVec 64) (st : State)
    (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = x)
    (hpc : st.pc = entry + testLoopOff)
    (hf0 : prog.fetch (entry + testLoopOff) = some (.addSubImm .W64 .ADD .x0 .x0 1#12 false))
    (hf1 : prog.fetch (entry + testNextOff) = some (.addSubImm .W64 .ADD .x0 .x0 2#12 false)) :
    SepWP prog (entry + (testLoopOff + 8#64)) st emp
      (sepPost (fun sf => sf.readReg64 .x0 = x + 3#64) emp) := by
  sym_block
  wp_done

theorem named_offset_abbrev_large_64bit_ok (prog : Program) (entry x : BitVec 64) (st : State)
    (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = x)
    (hpc : st.pc = entry + testLargeOff)
    (hf0 : prog.fetch (entry + 0x300000000#64) = some (.addSubImm .W64 .ADD .x0 .x0 5#12 false))
    (hf1 : prog.fetch (entry + 0x300000004#64) = some (.ret .lr)) :
    SepWP prog (st.readReg64 .lr) st emp
      (sepPost (fun sf => sf.readReg64 .x0 = x + 5#64) emp) := by
  sym_block
  wp_done

end NamedOffsetAbbrevTests

/-! ## Loop Back-Edges -/

section LoopBackEdgeTests

set_option maxHeartbeats 100000

abbrev loopHdrOff : BitVec 64 := 4#64 + 4#64

theorem loop_backedge_backward_sepwp_ok (prog : Program) (entry x n : BitVec 64) (st : State)
    (hrun : st.status = .Running)
    (hpc : st.pc = entry + 8#64)
    (hx0 : st.readReg64 .x0 = x)
    (hx1 : st.readReg64 .x1 = n)
    (hn : n ≠ 1#64)
    (hf0 : prog.fetch (entry + 8#64) = some (.addSubImm .W64 .ADD .x0 .x0 1#12 false))
    (hf1 : prog.fetch (entry + 12#64) = some (.addSubImm .W64 .SUBS .x1 .x1 1#12 false))
    (hf2 : prog.fetch (entry + 16#64) = some (.bCond .NE (-8#64))) :
    SepWP prog (entry + 8#64) st emp
      (sepPost (fun sf => sf.readReg64 .x0 = x + 1#64 ∧ sf.readReg64 .x1 = n - 1#64) emp) := by
  sym_block
  wp_done

theorem loop_backedge_with_abbrev_and_sp_sepwpp_ok (prog : Program) (entry baseSp n v : BitVec 64)
    (st : State)
    (hinv : st.readReg64 .sp = baseSp - 96#64 ∧ st.readReg64 .x1 = n ∧ st.status = .Running)
    (hpc : st.pc = entry + loopHdrOff)
    (halign : baseSp &&& 0xf#64 = 0#64)
    (hn : n ≠ 1#64)
    (hf0 : prog.fetch (entry + 8#64) = some (.ldr .W64 .X64 false .x0 (.Offset .sp 16#64)))
    (hf1 : prog.fetch (entry + 12#64) = some (.addSubImm .W64 .ADD .x0 .x0 1#12 false))
    (hf2 : prog.fetch (entry + 16#64) = some (.str .X64 .x0 (.Offset .sp 16#64)))
    (hf3 : prog.fetch (entry + 20#64) = some (.addSubImm .W64 .SUBS .x1 .x1 1#12 false))
    (hf4 : prog.fetch (entry + 24#64) = some (.bCond .NE (-16#64))) :
    SepWPp prog (entry + loopHdrOff) st
      ((baseSp - 80#64) ↦₆₄ v)
      (sepPost (fun sf => sf.readReg64 .x1 = n - 1#64) ((baseSp - 80#64) ↦₆₄ (v + 1#64)))
      (fun _ _ => True) := by
  sym_block
  wp_done

theorem loop_backedge_forward_rotated_ok (prog : Program) (entry x n : BitVec 64) (st : State)
    (hrun : st.status = .Running)
    (hpc : st.pc = entry + 0#64)
    (hx0 : st.readReg64 .x0 = x)
    (hx1 : st.readReg64 .x1 = n)
    (hn : n ≠ 1#64)
    (hf0 : prog.fetch (entry + 0#64) = some (.addSubImm .W64 .SUBS .x1 .x1 1#12 false))
    (hf1 : prog.fetch (entry + 4#64) = some (.bCond .NE 4#64))
    (_hf2 : prog.fetch (entry + 8#64) = some (.addSubImm .W64 .ADD .x0 .x0 99#12 false)) :
    SepWP prog (entry + 8#64) st emp
      (sepPost (fun sf => sf.readReg64 .x0 = x ∧ sf.readReg64 .x1 = n - 1#64) emp) := by
  sym_block
  wp_done

end LoopBackEdgeTests

end Testing.SymBlock
