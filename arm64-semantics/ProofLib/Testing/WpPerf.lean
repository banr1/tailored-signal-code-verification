/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.SepLogic.WP

/-!
# Normalization and Kernel Performance Regression Tests

Regression tests for `arm64_norm` and `wp_norm`: `#arm64_check_no_rfl_state_lemmas`, bitwise and
offset literal folding, 60-step `wp_steps` / `wp_sym_steps` symbolic execution within
`maxHeartbeats 50000`, `wp_clear_temps`, and spine-lifted `wp_sep_access` / `sep_entail`.
-/

@[expose] public section

namespace Testing.WpPerf

open Arm64 ProofLib

arm64_proof_prelude

/-! ## Guard against `rfl`-proved `Arm64.State` lemmas -/

#arm64_check_no_rfl_state_lemmas

section DeliberatelyBadRflStateLemma

@[local arm64_norm]
theorem deliberate_bad_rfl_state_lemma (s : State) (v : BitVec 64) :
    (s.setPC v).mem = s.mem := rfl

set_option trace.profiler false in
/--
error: Found `rfl`-proved `Arm64.State` lemmas in normalization simp sets (these cause O(2^N) kernel structure-eta blowups; prove them with `by cases s; rfl` or field lemmas instead):
  [arm64_norm] Testing.WpPerf.deliberate_bad_rfl_state_lemma
-/
#guard_msgs in
#arm64_check_no_rfl_state_lemmas

end DeliberatelyBadRflStateLemma

#arm64_check_no_rfl_state_lemmas

/-! ## Bitwise and offset literal normalization -/

section BitwiseLiteralNorm

set_option maxHeartbeats 50000

@[simp, arm64_norm] def bitwise_norm_addr : BitVec 64 := 0x20000#64

def bitwiseNormCode : FnCode :=
  .atAddr "bitwise_norm" bitwise_norm_addr
    ("12800000 " ++ -- 0x20000: movn w0, #0          -> x0 = 0x00000000ffffffff
     "92800001 " ++ -- 0x20004: movn x1, #0          -> x1 = 0xffffffffffffffff
     "aa2003e2 " ++ -- 0x20008: mvn  x2, x0          -> x2 = 0xffffffff00000000
     "aa220003 " ++ -- 0x2000c: orn  x3, x0, x2      -> x3 = 0x00000000ffffffff
     "8a200024 " ++ -- 0x20010: bic  x4, x1, x0      -> x4 = 0xffffffff00000000
     "ca210005 " ++ -- 0x20014: eon  x5, x0, x1      -> x5 = 0x00000000ffffffff
     "cb0003e6 " ++ -- 0x20018: neg  x6, x0          -> x6 = 0xffffffff00000001
     "93407c07 " ++ -- 0x2001c: sxtw x7, w0          -> x7 = 0xffffffffffffffff
     "ca050060 " ++ -- 0x20020: eor  x0, x3, x5      -> x0 = 0
     "8b070000 " ++ -- 0x20024: add  x0, x0, x7      -> x0 = 0xffffffffffffffff
     "d65f03c0")    -- 0x20028: ret

abbrev BitwiseNormCodeAt (prog : Program) : Prop :=
  bitwiseNormCode.holds prog

abbrev bitwiseNormSpec : Spec Unit where
  pre  := fun _ _s0 => emp
  post := fun _ _ sf =>
    ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧
     sf.readReg64 .x2 = 0xffffffff00000000#64 ∧
     sf.readReg64 .x3 = 0x00000000ffffffff#64 ∧
     sf.readReg64 .x4 = 0xffffffff00000000#64 ∧
     sf.readReg64 .x5 = 0x00000000ffffffff#64 ∧
     sf.readReg64 .x6 = 0xffffffff00000001#64 ∧
     sf.readReg64 .x7 = 0xffffffffffffffff#64⌝

theorem bitwise_norm_ok (prog : Program) (h_code : BitwiseNormCodeAt prog) :
    prog.subroutineOk "bitwise_norm" bitwiseNormSpec := by
  wp_init u s0
  wp_steps
  wp_done

example (x : BitVec 64) :
    (x + BitVec.ofNat 64 8) + BitVec.ofNat 64 16 = x + 24#64 := by
  simp only [reduceBitVecAddOfNat64, Nat.reduceAdd, Nat.reduceMod]

end BitwiseLiteralNorm

/-! ## Non-`rfl` `State` field projection normalization -/

section StateFieldProjectionNorm

set_option maxHeartbeats 50000

theorem state_mem_spine_norm (s0 : State) (b : BitVec 64) :
    s0.mem =
      ((((s0.writeReg64 .x0 1#64).writeReg64 .x1 2#64).advancePC).setPC (b + 0x400#64)).mem := by
  simp only [wp_norm, arm64_norm]

end StateFieldProjectionNorm

/-! ## 60-step rebased subroutine performance -/

section StraightLineRebasePerf

set_option maxHeartbeats 50000
arm64_proof_prelude

/-- Kept reducible along with `Program.fnOff` so `(perfBaseProg.rebase b H).fnAddr "perf_60_steps"`
    reduces to `b + 0x400#64`. -/
def perfBaseProg : Program where
  base := 0#64
  code := []
  symbols := [("perf_60_steps", 0x400)]

@[simp, arm64_norm]
theorem perfBaseProg_fnOff : perfBaseProg.fnOff "perf_60_steps" = 0x400 := rfl

def perf60StepsHex : List (BitVec 32) :=
  "f9400001 b4000041 d2800020 d2800042 12800003 aa2303e4 8b030042 f9000402 f9000803 f9000c04 91000442 91000442 91000442 91000442 f9000402 f9400405 910004a5 910004a5 910004a5 910004a5 f9000805 f9400806 910004c6 910004c6 910004c6 910004c6 f9000c06 f9400c07 910004e7 910004e7 910004e7 910004e7 f9000407 f9400402 91000442 91000442 91000442 91000442 f9000802 f9400803 91000463 91000463 91000463 91000463 f9000c03 f9400c04 91000484 91000484 91000484 91000484 f9000404 f9400405 910004a5 910004a5 910004a5 910004a5 f9000805 f9000c05 910004a0 91000400 d65f03c0"

structure Perf60Args where
  p  : BitVec 64
  f1 : BitVec 64
  f2 : BitVec 64
  f3 : BitVec 64

abbrev perf60StepsSpec : Spec Perf60Args where
  pre  := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.p⌝ ∗
    (a.p ↦₆₄ 0#64) ∗
    ((a.p + 8#64) ↦₆₄ a.f1) ∗
    ((a.p + 16#64) ↦₆₄ a.f2) ∗
    ((a.p + 24#64) ↦₆₄ a.f3)
  post := fun a _ sf =>
    ⌜sf.readReg64 .x0 = 0x100000023#64⌝ ∗
    (a.p ↦₆₄ 0#64) ∗
    ((a.p + 8#64) ↦₆₄ 0x10000001d#64) ∗
    ((a.p + 16#64) ↦₆₄ 0x100000021#64) ∗
    ((a.p + 24#64) ↦₆₄ 0x100000021#64)

theorem perf_60_steps_ok (b : BitVec 64) (H : String → Option (State → State))
    (h_code : (perfBaseProg.rebase b H).hasCode (b + 0x400#64) perf60StepsHex) :
    (perfBaseProg.rebase b H).subroutineOk "perf_60_steps" perf60StepsSpec := by
  wp_init a s0
  wp_steps
  wp_done

end StraightLineRebasePerf

/-! ## `SymM` symbolic execution (`wp_sym_steps`) -/

section SymWPPerf

set_option maxHeartbeats 50000
arm64_proof_prelude

theorem bitwise_norm_sym_ok (prog : Program) (h_code : BitwiseNormCodeAt prog) :
    prog.subroutineOk "bitwise_norm" bitwiseNormSpec := by
  wp_init u s0
  wp_sym_steps
  wp_done

theorem perf_60_steps_sym_ok (b : BitVec 64) (H : String → Option (State → State))
    (h_code : (perfBaseProg.rebase b H).hasCode (b + 0x400#64) perf60StepsHex) :
    (perfBaseProg.rebase b H).subroutineOk "perf_60_steps" perf60StepsSpec := by
  wp_init a s0
  wp_sym_steps
  wp_done

end SymWPPerf

/-! ## Dependency-aware `wp_clear_temps` and 32-atom `wp_sep_access_fast` -/

section ClearTempsAndLargeFrameTests

set_option maxHeartbeats 50000

theorem wp_clear_temps_topological_test (x : BitVec 64) :
    let v0_live : BitVec 64 := x + 1#64
    let v1_live : BitVec 64 := v0_live + 2#64
    let v0_dead : BitVec 64 := x + 10#64
    let v2_dead : BitVec 64 := v0_dead + 20#64
    have _hv2_dead : v2_dead = x + 30#64 := by dsimp [v2_dead, v0_dead]; bv_arith
    v1_live = x + 3#64 := by
  intro v0_live v1_live v0_dead v2_dead _hv2_dead
  have hvalid : v1_live = x + 3#64 := by dsimp [v1_live, v0_live]; bv_arith
  wp_clear_temps [v0_live, v1_live, v0_dead, v2_dead, _hv2_dead]
  let v3_dead : BitVec 64 := v1_live + 99#64
  have hv3_dead : v3_dead = v1_live + 99#64 := rfl
  wp_clear_temps
  exact hvalid

theorem wp_sep_access_fast_32_atoms (p : BitVec 64) (v : BitVec 64) (R : SepProp) :
    SepLoad64 (p + 248#64)
      ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 1#64) ∗ ((p + 16#64) ↦₆₄ 2#64) ∗ ((p + 24#64) ↦₆₄ 3#64) ∗
       ((p + 32#64) ↦₆₄ 4#64) ∗ ((p + 40#64) ↦₆₄ 5#64) ∗ ((p + 48#64) ↦₆₄ 6#64) ∗ ((p + 56#64) ↦₆₄ 7#64) ∗
       ((p + 64#64) ↦₆₄ 8#64) ∗ ((p + 72#64) ↦₆₄ 9#64) ∗ ((p + 80#64) ↦₆₄ 10#64) ∗ ((p + 88#64) ↦₆₄ 11#64) ∗
       ((p + 96#64) ↦₆₄ 12#64) ∗ ((p + 104#64) ↦₆₄ 13#64) ∗ ((p + 112#64) ↦₆₄ 14#64) ∗ ((p + 120#64) ↦₆₄ 15#64) ∗
       ((p + 128#64) ↦₆₄ 16#64) ∗ ((p + 136#64) ↦₆₄ 17#64) ∗ ((p + 144#64) ↦₆₄ 18#64) ∗ ((p + 152#64) ↦₆₄ 19#64) ∗
       ((p + 160#64) ↦₆₄ 20#64) ∗ ((p + 168#64) ↦₆₄ 21#64) ∗ ((p + 176#64) ↦₆₄ 22#64) ∗ ((p + 184#64) ↦₆₄ 23#64) ∗
       ((p + 192#64) ↦₆₄ 24#64) ∗ ((p + 200#64) ↦₆₄ 25#64) ∗ ((p + 208#64) ↦₆₄ 26#64) ∗ ((p + 216#64) ↦₆₄ 27#64) ∗
       ((p + 224#64) ↦₆₄ 28#64) ∗ ((p + 232#64) ↦₆₄ 29#64) ∗ ((p + 240#64) ↦₆₄ 30#64) ∗ ((p + 248#64) ↦₆₄ᵣ v) ∗ R)
      v := by
  wp_sep_access_fast

theorem allocSeq_identical_req_disjoint {m : Memory} (alloc : ProofLib.Allocator) (req : BitVec 64)
    (R : SepProp)
    (h : m ⊨ alloc.allocSeq 0 [(req, 8), (req, 8)] ∗ R)
    (h0 : alloc.ptr 0 req ≠ 0#64) (h1 : alloc.ptr 1 req ≠ 0#64) :
    alloc.ptr 0 req ≠ alloc.ptr 1 req :=
  ProofLib.Allocator.allocSeq_pair_ne h h0 h1 (by decide) (by decide)

end ClearTempsAndLargeFrameTests

/-! ## Spine-lifted `wp_sep_access` and sorted-index AC certificates -/

section SpineAccessTests

set_option maxHeartbeats 50000

theorem wp_sep_access_store_left_nested (p v w : BitVec 64) (R : SepProp) :
    SepStore64 ((p + 8#64) + 8#64) w
      ((((p ↦₆₄ 0#64) ∗ ((p + 16#64) ↦₆₄ v)) ∗ ((p + 8#64) ↦₆₄ 1#64)) ∗ R)
      ((((p ↦₆₄ 0#64) ∗ ((p + 16#64) ↦₆₄ w)) ∗ ((p + 8#64) ↦₆₄ 1#64)) ∗ R) := by
  wp_sep_access

theorem wp_sep_access_store_infers_post (p v w : BitVec 64) (R : SepProp) :
    ∃ P', SepStore64 (p + 8#64) w (R ∗ ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ v))) P' := by
  apply Exists.intro
  wp_sep_access

theorem wp_sep_access_store16 (p : BitVec 64) (h h' : BitVec 16) (R : SepProp) :
    SepStore16 (p + 4#64) h' (R ∗ ((p ↦₃₂ 0#32) ∗ ((p + 4#64) ↦₁₆ h)))
      (R ∗ ((p ↦₃₂ 0#32) ∗ ((p + 4#64) ↦₁₆ h'))) := by
  wp_sep_access

theorem wp_sep_access_store32 (p : BitVec 64) (x x' : BitVec 32) (R : SepProp) :
    SepStore32 p x' (R ∗ ((p ↦₃₂ x) ∗ ((p + 4#64) ↦₁₆ 0#16)))
      (R ∗ ((p ↦₃₂ x') ∗ ((p + 4#64) ↦₁₆ 0#16))) := by
  wp_sep_access

theorem wp_sep_access_load8_ro (p : BitVec 64) (b : BitVec 8) (R : SepProp) :
    SepLoad8 (p + 2#64) (((p ↦₁₆ 0#16) ∗ ((p + 2#64) ↦₈ᵣ b)) ∗ R) b := by
  wp_sep_access

theorem wp_sep_access_load8_from32 (p : BitVec 64) (R : SepProp) :
    ∃ v, SepLoad8 (p + 1#64) (R ∗ (p ↦₃₂ 0x44332211#32)) v := by
  apply Exists.intro
  wp_sep_access

theorem wp_sep_access_load16_bytes (p : BitVec 64) (R : SepProp) :
    SepLoad16 (p + 2#64) (R ∗ (p ↦ᵣ [0x11#8, 0x22#8, 0x33#8, 0x44#8])) 0x4433#16 := by
  wp_sep_access

theorem sep_entail_reverse_40 (p : BitVec 64) (m : Memory)
    (h : m ⊨ (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 1#64) ∗ ((p + 16#64) ↦₆₄ 2#64) ∗ ((p + 24#64) ↦₆₄ 3#64) ∗
      ((p + 32#64) ↦₆₄ 4#64) ∗ ((p + 40#64) ↦₆₄ 5#64) ∗ ((p + 48#64) ↦₆₄ 6#64) ∗ ((p + 56#64) ↦₆₄ 7#64) ∗
      ((p + 64#64) ↦₆₄ 8#64) ∗ ((p + 72#64) ↦₆₄ 9#64) ∗ ((p + 80#64) ↦₆₄ 10#64) ∗ ((p + 88#64) ↦₆₄ 11#64) ∗
      ((p + 96#64) ↦₆₄ 12#64) ∗ ((p + 104#64) ↦₆₄ 13#64) ∗ ((p + 112#64) ↦₆₄ 14#64) ∗ ((p + 120#64) ↦₆₄ 15#64) ∗
      ((p + 128#64) ↦₆₄ 16#64) ∗ ((p + 136#64) ↦₆₄ 17#64) ∗ ((p + 144#64) ↦₆₄ 18#64) ∗ ((p + 152#64) ↦₆₄ 19#64)) :
    m ⊨ ((p + 152#64) ↦₆₄ 19#64) ∗ ((p + 144#64) ↦₆₄ 18#64) ∗ ((p + 136#64) ↦₆₄ 17#64) ∗ ((p + 128#64) ↦₆₄ 16#64) ∗
      ((p + 120#64) ↦₆₄ 15#64) ∗ ((p + 112#64) ↦₆₄ 14#64) ∗ ((p + 104#64) ↦₆₄ 13#64) ∗ ((p + 96#64) ↦₆₄ 12#64) ∗
      ((p + 88#64) ↦₆₄ 11#64) ∗ ((p + 80#64) ↦₆₄ 10#64) ∗ ((p + 72#64) ↦₆₄ 9#64) ∗ ((p + 64#64) ↦₆₄ 8#64) ∗
      ((p + 56#64) ↦₆₄ 7#64) ∗ ((p + 48#64) ↦₆₄ 6#64) ∗ ((p + 40#64) ↦₆₄ 5#64) ∗ ((p + 32#64) ↦₆₄ 4#64) ∗
      ((p + 24#64) ↦₆₄ 3#64) ∗ ((p + 16#64) ↦₆₄ 2#64) ∗ ((p + 8#64) ↦₆₄ 1#64) ∗ (p ↦₆₄ 0#64) := by
  sep_entail

/--
error: wp_sep_access: no cell at p + 16#64 in
  p ↦₆₄ 0#64 ∗ (p + 8#64) ↦₆₄ 1#64
-/
#guard_msgs in
example (p : BitVec 64) :
    ∃ v, SepLoad64 (p + 16#64) ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 1#64)) v := by
  apply Exists.intro
  wp_sep_access

/--
error: wp_sep_access: no cell at p + 8#64 in
  p ↦₆₄ 0#64 ∗ (p + 8#64) ↦₆₄ᵣ 1#64
-/
#guard_msgs in
example (p w : BitVec 64) :
    ∃ P', SepStore64 (p + 8#64) w ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ᵣ 1#64)) P' := by
  apply Exists.intro
  wp_sep_access

end SpineAccessTests

end Testing.WpPerf
