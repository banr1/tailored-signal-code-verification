/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Object.Placed
public import Arm64.Trusted.Surface.IncludeBytes

/-!
# Compiled Binary Test Fixture

Static `Obj.PlacedLib` fixture extracted from a compiled `rustc -O` AArch64 object archive
(`CompiledBinaryFixture.bin`), providing 77 exported subroutines and 7 `.rodata` objects for
`Arm64.Testing.Generators.CompiledBinary`.
-/

@[expose] public section

namespace Testing.Generators

open Arm64

set_option maxHeartbeats 10000000
set_option maxRecDepth 2000000

def fixturePlacedCode : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 0 2272
def fixturePlacedData0 : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 2272 24
def fixturePlacedData1 : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 2296 17
def fixturePlacedData2 : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 2313 16
def fixturePlacedData3 : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 2329 24
def fixturePlacedData4 : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 2353 24
def fixturePlacedData5 : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 2377 24
def fixturePlacedData6 : List (BitVec 8) := include_bytes% "CompiledBinaryFixture.bin" 2401 24

def fixtureText : Obj.CodeBlock where
  code := fixturePlacedCode
  align := 4
  symbols := [
    ("abs_i64_csneg", 0x0),
    ("add128_u64", 0xc),
    ("aes", 0x18),
    ("arith_shift", 0x20),
    ("bswap_and_clz_u64", 0x30),
    ("cbz_fallback", 0x48),
    ("clamp_and_store", 0x5c),
    ("control_flow", 0x88),
    ("countdown_add_loop", 0x98),
    ("decoder_bug_regressions", 0xac),
    ("divmod_u64", 0xc0),
    ("dup_umov", 0xd0),
    ("fmov", 0xdc),
    ("mix_step", 0xe8),
    ("tag_finalize", 0xf4),
    ("hash_pair_and_store", 0xfc),
    ("auth_counter_send", 0x124),
    ("foo", 0x15c),
    ("baz", 0x164),
    ("bar", 0x16c),
    ("twoCalls", 0x184),
    ("outer", 0x1a0),
    ("leafTailCall", 0x1b8),
    ("callThenTailCall", 0x1c0),
    ("swap_and_accumulate", 0x1d8),
    ("rotate_and_commit_ctx", 0x200),
    ("machine_code_max", 0x230),
    ("machine_code_rev_shift", 0x23c),
    ("max_u64_branch", 0x248),
    ("max_u64_csel", 0x258),
    ("mem_countdown_loop", 0x264),
    ("move_2_regs_to_heap", 0x284),
    ("publish", 0x298),
    ("q_spill", 0x2a8),
    ("reg_offset", 0x2b4),
    ("shift_add_sub", 0x2c8),
    ("smaddl_sdiv_i64", 0x2d4),
    ("sort3_in_place", 0x2ec),
    ("stack_frame", 0x348),
    ("stack_spill_struct_update", 0x35c),
    ("stur_disjoint", 0x384),
    ("stur_ldur", 0x390),
    ("stur_ldur_sizes", 0x39c),
    ("swap_mem64", 0x3c0),
    ("sys_and_simd_pair", 0x3d4),
    ("tiered_fee_schedule", 0x3e8),
    ("transfer_balance", 0x430),
    ("validate_packet_header", 0x478),
    ("vec_alu", 0x4d4),
    ("vec_swap", 0x4e8),
    ("xor_swap", 0x4f8),
    ("__rustc::rust_begin_unwind", 0x508),
    ("examples::algorithms::vec_binary_search", 0x518),
    ("examples::algorithms::gcd_u64", 0x554),
    ("examples::algorithms::pow_u64", 0x570),
    ("examples::algorithms::uf_find", 0x5a0),
    ("examples::algorithms::uf_union", 0x5b8),
    ("examples::algorithms::fnv1a_u64", 0x5ec),
    ("examples::functions::bit_tricks", 0x624),
    ("examples::functions::arith_shift", 0x634),
    ("examples::functions::slice_index", 0x640),
    ("examples::functions::abs_diff_u64", 0x648),
    ("examples::functions::pair_sum_diff", 0x654),
    ("examples::functions::countdown_loop", 0x668),
    ("examples::functions::checked_add_u64", 0x67c),
    ("examples::functions::extract_bitfield", 0x68c),
    ("examples::functions::widening_mul_u64", 0x69c),
    ("examples::functions::saturating_add_u64", 0x6ac),
    ("examples::functions::bad", 0x6b8),
    ("examples::functions::max_u64", 0x6e0),
    ("examples::functions::mem_swap", 0x6ec),
    ("examples::functions::clamp_u64", 0x700),
    ("examples::functions::pair_copy", 0x714),
    ("examples::syscalls::app::slice_get_or_panic", 0x720),
    ("examples::syscalls::app::brk_alloc_and_write", 0x74c),
    ("examples::syscalls::app::alloc_write_and_exit", 0x794),
    ("examples::syscalls::app::checked_div_or_panic", 0x7e0),
    ("examples::syscalls::app::mmap_alloc_and_log_dual", 0x80c),
    ("examples::syscalls::app::mmap_stderr_and_exit_group", 0x884),
    ("rust_eh_personality", 0x8dc)]
  relocs := [
    { off := 540, kind := .call26, sym := "mix_step" },
    { off := 1736, kind := .adrpHi21, sym := "examples:.rodata..Lanon.0" },
    { off := 1740, kind := .addLo12, sym := "examples:.rodata..Lanon.0" },
    { off := 1744, kind := .adrpHi21, sym := "examples:.rodata..Lanon.2" },
    { off := 1748, kind := .addLo12, sym := "examples:.rodata..Lanon.2" },
    { off := 1756, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking5panic" },
    { off := 1848, kind := .adrpHi21, sym := "examples:.rodata..Lanon.4" },
    { off := 1852, kind := .addLo12, sym := "examples:.rodata..Lanon.4" },
    { off := 1864, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 2036, kind := .adrpHi21, sym := "examples:.rodata..Lanon.5" },
    { off := 2040, kind := .addLo12, sym := "examples:.rodata..Lanon.5" },
    { off := 2044, kind := .adrpHi21, sym := "examples:.rodata..Lanon.6" },
    { off := 2048, kind := .addLo12, sym := "examples:.rodata..Lanon.6" },
    { off := 2056, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking5panic" }]
  externs := [
    "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check",
    "_RNvNtCskxtBwYRO61I_4core9panicking5panic"]

def fixtureData : List Obj.SymDataInfo := [
  { sym := "examples:.rodata..Lanon.0"
    align := 1
    readOnly := true
    bytes := fixturePlacedData0
    zeroTail := 0
    relocs := [] },
  { sym := "examples:.rodata.str1.1+0x0"
    align := 1
    readOnly := true
    bytes := fixturePlacedData1
    zeroTail := 0
    relocs := [] },
  { sym := "examples:.rodata.str1.1+0x11"
    align := 1
    readOnly := true
    bytes := fixturePlacedData2
    zeroTail := 0
    relocs := [] },
  { sym := "examples:.rodata..Lanon.2"
    align := 8
    readOnly := true
    bytes := fixturePlacedData3
    zeroTail := 0
    relocs := [
      { off := 0, kind := .abs64, sym := "examples:.rodata.str1.1+0x0" }] },
  { sym := "examples:.rodata..Lanon.4"
    align := 8
    readOnly := true
    bytes := fixturePlacedData4
    zeroTail := 0
    relocs := [
      { off := 0, kind := .abs64, sym := "examples:.rodata.str1.1+0x11" }] },
  { sym := "examples:.rodata..Lanon.5"
    align := 1
    readOnly := true
    bytes := fixturePlacedData5
    zeroTail := 0
    relocs := [] },
  { sym := "examples:.rodata..Lanon.6"
    align := 8
    readOnly := true
    bytes := fixturePlacedData6
    zeroTail := 0
    relocs := [
      { off := 0, kind := .abs64, sym := "examples:.rodata.str1.1+0x11" }] }
]

/-- Static `Obj.PlacedLib` test fixture of compiled Rust routines and read-only data. -/
def fixturePlacedLib : Obj.PlacedLib where
  name := "examples"
  text := fixtureText
  data := fixtureData
  exports := [
    "abs_i64_csneg",
    "add128_u64",
    "aes",
    "arith_shift",
    "bswap_and_clz_u64",
    "cbz_fallback",
    "clamp_and_store",
    "control_flow",
    "countdown_add_loop",
    "decoder_bug_regressions",
    "divmod_u64",
    "dup_umov",
    "fmov",
    "mix_step",
    "tag_finalize",
    "hash_pair_and_store",
    "auth_counter_send",
    "foo",
    "baz",
    "bar",
    "twoCalls",
    "outer",
    "leafTailCall",
    "callThenTailCall",
    "swap_and_accumulate",
    "rotate_and_commit_ctx",
    "machine_code_max",
    "machine_code_rev_shift",
    "max_u64_branch",
    "max_u64_csel",
    "mem_countdown_loop",
    "move_2_regs_to_heap",
    "publish",
    "q_spill",
    "reg_offset",
    "shift_add_sub",
    "smaddl_sdiv_i64",
    "sort3_in_place",
    "stack_frame",
    "stack_spill_struct_update",
    "stur_disjoint",
    "stur_ldur",
    "stur_ldur_sizes",
    "swap_mem64",
    "sys_and_simd_pair",
    "tiered_fee_schedule",
    "transfer_balance",
    "validate_packet_header",
    "vec_alu",
    "vec_swap",
    "xor_swap",
    "examples::algorithms::vec_binary_search",
    "examples::algorithms::gcd_u64",
    "examples::algorithms::pow_u64",
    "examples::algorithms::uf_find",
    "examples::algorithms::uf_union",
    "examples::algorithms::fnv1a_u64",
    "examples::functions::bit_tricks",
    "examples::functions::arith_shift",
    "examples::functions::slice_index",
    "examples::functions::abs_diff_u64",
    "examples::functions::pair_sum_diff",
    "examples::functions::countdown_loop",
    "examples::functions::checked_add_u64",
    "examples::functions::extract_bitfield",
    "examples::functions::widening_mul_u64",
    "examples::functions::saturating_add_u64",
    "examples::functions::bad",
    "examples::functions::max_u64",
    "examples::functions::mem_swap",
    "examples::functions::clamp_u64",
    "examples::functions::pair_copy",
    "examples::syscalls::app::slice_get_or_panic",
    "examples::syscalls::app::brk_alloc_and_write",
    "examples::syscalls::app::alloc_write_and_exit",
    "examples::syscalls::app::checked_div_or_panic",
    "examples::syscalls::app::mmap_alloc_and_log_dual",
    "examples::syscalls::app::mmap_stderr_and_exit_group"]

end Testing.Generators
