/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.GrowOneSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.Placed.BridgeReloc
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable `RustAlloc` Proofs for Sysroot `RawVec::grow_one` (Blocks 619..622)

Verifies the in-image `liballoc` and `libstd` `RawVec::{grow_one, finish_grow}` blocks
against parametric `RustAlloc A` contracts:
- Block 620 (`finish_grow [liballoc]`, `stride = 1, align = 1`) and block 619
  (`RawVec<u8>::grow_one`).
- Block 622 (`finish_grow [libstd]`, generic `(stride, align)`) and block 621
  (`RawVec<Vec<u8>>::grow_one`, including `MergeFunctions` symbol aliases).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

gen_ls_blk 619
gen_ls_blk 620
gen_ls_blk 621
gen_ls_blk 622

/-!
## `MergeFunctions` Alias Resolutions for Block 621

`gen_ls_blk 621` emits resolution lemmas for the first symbol in block 621's symbol table;
the lemmas below resolve the remaining five 24-byte/8-aligned aliases at offset 0.
-/

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_621_lineRow (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "<alloc::raw_vec::RawVec<addr2line::line::LineRow>>::grow_one" =
      pl.base 621 :=
  ls_resolve_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<addr2line::line::LineRow>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_fnAddr_blk_621_lineRow (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl "<alloc::raw_vec::RawVec<addr2line::line::LineRow>>::grow_one" =
      pl.base 621 :=
  ls_fnAddr_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<addr2line::line::LineRow>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_621_string (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "<alloc::raw_vec::RawVec<alloc::string::String>>::grow_one" =
      pl.base 621 :=
  ls_resolve_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<alloc::string::String>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_fnAddr_blk_621_string (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl "<alloc::raw_vec::RawVec<alloc::string::String>>::grow_one" =
      pl.base 621 :=
  ls_fnAddr_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<alloc::string::String>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_621_vecU8 (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" =
      pl.base 621 :=
  ls_resolve_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_fnAddr_blk_621_vecU8 (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" =
      pl.base 621 :=
  ls_fnAddr_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_621_attrVal (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl
      "<alloc::raw_vec::RawVec<gimli::read::unit::AttributeValue<gimli::read::endian_slice::EndianSlice<gimli::endianity::LittleEndian>, usize>>>::grow_one" =
      pl.base 621 :=
  ls_resolve_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<gimli::read::unit::AttributeValue<gimli::read::endian_slice::EndianSlice<gimli::endianity::LittleEndian>, usize>>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_fnAddr_blk_621_attrVal (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl
      "<alloc::raw_vec::RawVec<gimli::read::unit::AttributeValue<gimli::read::endian_slice::EndianSlice<gimli::endianity::LittleEndian>, usize>>>::grow_one" =
      pl.base 621 :=
  ls_fnAddr_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<gimli::read::unit::AttributeValue<gimli::read::endian_slice::EndianSlice<gimli::endianity::LittleEndian>, usize>>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_621_osString (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "<alloc::raw_vec::RawVec<std::ffi::os_str::OsString>>::grow_one" =
      pl.base 621 :=
  ls_resolve_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<std::ffi::os_str::OsString>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_fnAddr_blk_621_osString (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl "<alloc::raw_vec::RawVec<std::ffi::os_str::OsString>>::grow_one" =
      pl.base 621 :=
  ls_fnAddr_block_chars
    (cs := str_chars% "<alloc::raw_vec::RawVec<std::ffi::os_str::OsString>>::grow_one")
    (by rfl_kernel) (by decide +kernel)

theorem ls_resolve_growOneU8Name (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl LibsignalSpqrV1.growOneU8Name = pl.base 619 :=
  ls_resolve_blk_619 pl

theorem ls_fnAddr_growOneU8Name (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl LibsignalSpqrV1.growOneU8Name = pl.base 619 :=
  ls_fnAddr_blk_619 pl

theorem ls_resolve_growOneVecU8Name (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl LibsignalSpqrV1.growOneVecU8Name = pl.base 621 :=
  ls_resolve_blk_621_vecU8 pl

theorem ls_fnAddr_growOneVecU8Name (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl LibsignalSpqrV1.growOneVecU8Name = pl.base 621 :=
  ls_fnAddr_blk_621_vecU8 pl

namespace SpqrV1.Alloc

open Arm64 Arm64.Obj ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open DoReserveNorm GrowOneNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## External Hook and Code-Loaded Helpers -/

theorem spqr_externAt?_of_mem_623 [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

theorem spqr_hook_ok_of_mem_623 [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by simp [hk, hget]) hsat hi hunmut

/-- Weakens `withLsCodeLoaded` to `LibsignalTripleRatchet.withLsCodeRoLoaded`. -/
theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_alloc {α : Type} {prog : Program}
    {pl : MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hcro, hpre⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcro.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-! ## Arithmetic and Stack Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]
  omega

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

private theorem stackAt_growOne_local (sp : BitVec 64) :
    stackAt sp growOneStack =
      stackAt (sp - 64#64) finishGrowStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve_gen sp (hookStack := allocHookStack) (by decide)

private theorem grow_new_cap_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 4 < 2 * cap.toNat at hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 4 < 2 * cap.toNat at hc
    change 4 = max (2 * cap.toNat) 4
    omega

private theorem grow_new_cap_u8_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 8 < 2 ^ 63) :
    (if (8#64).ult (cap <<< 1) = true then cap <<< 1 else 8#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 8) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (8#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 8 < 2 * cap.toNat at hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 8 < 2 * cap.toNat at hc
    change 8 = max (2 * cap.toNat) 8
    omega

/-! ## Block 620: `finish_grow [liballoc]` (`stride = 1, align = 1`) -/

private def finishGrow1AllocSpecG_b2 (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) }

private def finishGrow1ReallocSpecG_b2 (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_1_placed_of_zero_ne_b2 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG_b2 A hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG_b2 A hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG_b2,
      FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine hne.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG_b2,
      FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

private theorem finish_grow_620_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1AllocSpecG_b2 A hookStack) := by
  unfold finishGrow1AllocSpecG_b2 finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

private theorem finish_grow_620_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1ReallocSpecG_b2 A hookStack) := by
  unfold finishGrow1ReallocSpecG_b2 finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

theorem finish_grow_620_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1SpecWithStack A hookStack) :=
  finish_grow_1_placed_of_zero_ne_b2
    (finish_grow_620_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_620_ne_placed_ok_of_hooks hhook hrealloc)

/-- Block 620 (`finish_grow [liballoc]`) meets `finishGrow1Spec A`. -/
theorem finish_grow_620_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1Spec A) :=
  finish_grow_620_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem_623 hshim))
    (spqr_hook_ok_of_mem_623 halloc)
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem_623 hrealloc) (by decide) (by decide))

theorem finish_grow_620_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1SpecX A) :=
  finish_grow_620_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem_623 hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem_623 halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem_623 hrealloc) (by decide) (by decide))

/-! ## Block 622: `finish_grow [libstd]` (Generic `stride` and `align`) -/

private def finishGrow8AllocSpecG_b2 (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 48) }

private def finishGrow8ReallocSpecG_b2 (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
        (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 48) }

private theorem finish_grow_622_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrow8AllocSpecG_b2 A hookStack) := by
  unfold finishGrow8AllocSpecG_b2 finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  subst cap
  subst bs
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf]
    wp_done

private theorem finish_grow_622_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrow8ReallocSpecG_b2 A hookStack) := by
  unfold finishGrow8ReallocSpecG_b2 finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : LayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨hold_pos, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  wp_steps
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]
    wp_done

theorem finish_grow_622_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrowSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_622_zero_placed_ok_of_hooks hhook hshim halloc).mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrowSpecWithStack, finishGrow8AllocSpecG_b2,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_622_ne_placed_ok_of_hooks hhook hrealloc).mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrowSpecWithStack, finishGrow8ReallocSpecG_b2,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-- Block 622 (`finish_grow [libstd]`) meets `finishGrowSpec A`. -/
theorem finish_grow_622_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrowSpec A) :=
  finish_grow_622_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem_623 hshim))
    (spqr_hook_ok_of_mem_623 halloc)
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem_623 hrealloc) (by decide) (by decide))

theorem finish_grow_622_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrowSpecX A) :=
  finish_grow_622_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem_623 hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem_623 halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem_623 hrealloc) (by decide) (by decide))

/-! ## Block 619: `RawVec<u8>::grow_one` -/

/-- Stack budget `(allocHookStack + 32) + 64` (`4192` B) for `RawVec<u8>::grow_one`. -/
abbrev growOneU8SmallStack : Nat := (allocHookStack + 32) + 64

/-- Prefix-preserving contract (`bs.length ≤ cap.toNat`) for `RawVec<u8>::grow_one` at `growOneU8SmallStack`. -/
def growOneU8BsSpec (A : RustAlloc) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 8 < 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
    A.pool ∗ stackAt s.sp growOneU8SmallStack
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗
      (v ↦₆₄ newCapU8 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 8) 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 8 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp growOneU8SmallStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def growOneU8BsZeroSpec (A : RustAlloc) : Spec GrowGhost :=
  { growOneU8BsSpec A with
    pre := fun (v, cap, ptr, bs) s =>
      ⌜s.readReg64 .x0 = v ∧ cap = 0#64 ∧ bs = [] ∧ ptr ≠ 0#64 ∧
        max (2 * cap.toNat) 8 < 2 ^ 63⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      A.pool ∗ stackAt s.sp growOneU8SmallStack }

private def growOneU8BsNeSpec (A : RustAlloc) : Spec GrowGhost :=
  { growOneU8BsSpec A with
    pre := fun (v, cap, ptr, bs) s =>
      ⌜s.readReg64 .x0 = v ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧ ptr ≠ 0#64 ∧
        max (2 * cap.toNat) 8 < 2 ^ 63⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.pool ∗ stackAt s.sp growOneU8SmallStack }

private theorem growOneU8_bs_zero_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base (finishGrow1Spec A)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BsZeroSpec A)) := by
  unfold withLsCodeLoaded growOneU8BsZeroSpec growOneU8BsSpec growOneU8SmallStack newCapU8
  simp only [stackAt_doReserve32_gen _ (hookStack := allocHookStack) (by decide), sepExists_sepConj_right]
  have hpanic : ((blkPC_619).rebase (blkPl_619).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem_623).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hcap0 : cap = 0#64 := by assumption
  have hbs : bs = [] := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 8 < 2 ^ 63 := by assumption
  have hnew_eq := grow_new_cap_u8_eq_local hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 8)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 8 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  subst hcap0
  subst hbs
  have hnew_eq0 : (if (8#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 8#64) = new := hnew_eq
  have hmax_eq : max (2 * 0) 8 = new.toNat := by rw [hnew_toNat]; rfl
  simp only [pointsToBytes_nil,
    List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmax_eq]
  clear hmax_eq
  apply SepWPp.of_sepWP (mid := (blkPl_619).base + 52#64)
  wp_steps_lscl (lsmpl.base 620)
  have hfg0 := lscall_blk (callerProg := (blkPC_619).rebase (blkPl_619).base H)
    (finish_grow_24_zero_cells_placed_of_spec (hookStack := allocHookStack) hfg) ‹_›
  wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases htag : w = 1#64
  · simp only [htag, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · simp only [htag, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
    subst hw0
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

private theorem growOneU8_bs_ne_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base (finishGrow1Spec A)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BsNeSpec A)) := by
  unfold withLsCodeLoaded growOneU8BsNeSpec growOneU8BsSpec growOneU8SmallStack newCapU8
  simp only [stackAt_doReserve32_gen _ (hookStack := allocHookStack) (by decide), sepExists_sepConj_right]
  have hpanic : ((blkPC_619).rebase (blkPl_619).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem_623).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hcap0 : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 8 < 2 ^ 63 := by assumption
  have hnew_eq := grow_new_cap_u8_eq_local hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 8)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 8 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  simp only [sepConj_assoc]
  have hsub_eq : max (2 * cap.toNat) 8 - bs.length = new.toNat - bs.length := by
    rw [hnew_toNat]
  have hmax_eq : max (2 * cap.toNat) 8 = new.toNat := by
    rw [hnew_toNat]
  rw [hsub_eq, hmax_eq]
  clear hsub_eq hmax_eq
  apply SepWPp.of_sepWP (mid := (blkPl_619).base + 52#64)
  wp_steps_lscl (lsmpl.base 620)
  have hfg1 := lscall_blk (callerProg := (blkPC_619).rebase (blkPl_619).base H)
    (finish_grow_24_ne_cells_placed_of_spec (hookStack := allocHookStack) hfg) ‹_›
  wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases htag : w = 1#64
  · simp only [htag, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · simp only [htag, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
    subst hw0
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-- Block 619 (`RawVec<u8>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneU8BsSpec A)`. -/
theorem growOneU8_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base (finishGrow1Spec A)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BsSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : cap = 0#64
  · refine (growOneU8_bs_zero_placed_ok_of_fg h_panic hfg).mono_outcome
      (v, cap, ptr, bs) R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
    dsimp only [withLsCodeLoaded, growOneU8BsSpec, growOneU8BsZeroSpec] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hbs_le, hptr, hbound⟩, hmem⟩
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by subst hcap0; exact Nat.eq_zero_of_le_zero hbs_le)
    exact ⟨⟨hx0, trivial, hbs, hptr, hbound⟩, hmem⟩
  · refine (growOneU8_bs_ne_placed_ok_of_fg h_panic hfg).mono_outcome
      (v, cap, ptr, bs) R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
    dsimp only [withLsCodeLoaded, growOneU8BsSpec, growOneU8BsNeSpec] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hbs_le, hptr, hbound⟩, hmem⟩
    exact ⟨⟨hx0, hcap0, hbs_le, hptr, hbound⟩, hmem⟩

theorem growOneU8_placed_cl_ok_of_bs [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneU8BsSpec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneU8Spec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12192
  have hstack : stackAt s0.sp extHookStack = Frame ∗ stackAt s0.sp growOneU8SmallStack :=
    ProofLib.stackAt_split_bottom s0.sp growOneU8SmallStack 12192 (by decide)
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  simp only [growOneU8Spec, BitVec.ofNat_eq_ofNat, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneU8BsSpec A)).pre (x.v, x.cap, x.ptr, x.bs) s0 ∗ (Frame ∗ R) := by
    dsimp only [withLsCodeLoaded, growOneU8BsSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound⟩, ?_⟩
    rw [hstack] at hmem
    by_cases hcap0 : x.cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hbs.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, growOneU8BsSpec, growOneU8Spec] at hq ⊢
    rw [hstack]
    simp only [hlen, BitVec.ofNat_eq_ofNat] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    dsimp only [withLsCodeLoaded, growOneU8BsSpec, growOneU8Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact False.elim (allowPanic_not_exited hq)
  · exact False.elim (allowPanic_not_exited hq)

theorem growOneU8_placed_cl_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base (finishGrow1Spec A)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8Spec A)) :=
  growOneU8_placed_cl_ok_of_bs (growOneU8_bs_placed_ok_of_fg h_panic hfg)

/-- Block 619 (`RawVec<u8>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneU8Spec A)`. -/
theorem growOneU8_placed_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8Spec A)) :=
  growOneU8_placed_cl_ok_of_fg h_panic (finish_grow_620_placed_ok hshim halloc hrealloc)

/-- Own-block `blockProgram` contract for block 619 (`growOneU8Spec A`). -/
theorem growOneU8_blockProgram_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 619 H)
      (lsmpl.base 619)
      (withLsCodeLoaded lsmpl (growOneU8Spec A)) := by
  rw [← (instIsLsBlockProg_619 H).eq_blockProgram]
  exact growOneU8_placed_cl_ok h_panic hshim halloc hrealloc

/-! ## Block 621: `RawVec<Vec<u8>>::grow_one` -/

/-- Block 621 (`RawVec<Vec<u8>>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneStrideBsSpec A 24 8)`. -/
theorem growOneVecU8_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base (finishGrowSpec A)) :
    subroutine_ok ((blkPC_621).rebase (blkPl_621).base H)
      (blkPl_621).base
      (withLsCodeLoaded lsmpl (growOneStrideBsSpec A 24 8)) := by
  unfold withLsCodeLoaded
  simp only [growOneStrideBsSpec, stackAt_growOne_local, sepExists_sepConj_right]
  have hpanic : ((blkPC_621).rebase (blkPl_621).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem_623).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq_local hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (24#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 24; omega, hpow, ?_⟩
    change new.toNat * 24 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 24 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 24 = new.toNat * 24 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_621).base + 60#64)
    wp_steps_lscl (lsmpl.base 622)
    have hfg0 := lscall_blk (callerProg := (blkPC_621).rebase (blkPl_621).base H)
      (finish_grow_8_zero_cells_placed_of_spec (hookStack := allocHookStack) hfg) ‹_›
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 24#64, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : max (2 * cap.toNat) 4 * 24 - bs.length = new.toNat * 24 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 24 = new.toNat * 24 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_621).base + 60#64)
    wp_steps_lscl (lsmpl.base 622)
    have hfg1 := lscall_blk (callerProg := (blkPC_621).rebase (blkPl_621).base H)
      (finish_grow_8_ne_cells_placed_of_spec (hookStack := allocHookStack) hfg) ‹_›
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 8#64, 24#64, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem growOneVecU8_placed_cl_ok_of_full [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (hfull : subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneStrideFullSpec A 24 8))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneVecU8Spec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12176
  have hstack : stackAt s0.sp extHookStack = Frame ∗ stackAt s0.sp growOneStack :=
    ProofLib.stackAt_split_bottom s0.sp growOneStack 12176 (by decide)
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  simp only [growOneVecU8Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOneStrideFullSpec A 24 8)).pre (x.v, x.cap, x.ptr, x.bs) s0 ∗
        (Frame ∗ R) := by
    dsimp only [withLsCodeLoaded, growOneStrideFullSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hptr, hbound⟩, ?_⟩
    rw [hstack] at hmem
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hfull.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, growOneStrideFullSpec, growOneVecU8Spec, newCapVecU8] at hq ⊢
    rw [hstack]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    dsimp only [withLsCodeLoaded, growOneStrideFullSpec, growOneVecU8Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact False.elim (allowPanic_not_exited hq)
  · exact False.elim (allowPanic_not_exited hq)

theorem growOneVecU8_placed_cl_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base (finishGrowSpec A)) :
    subroutine_ok ((blkPC_621).rebase (blkPl_621).base H)
      (blkPl_621).base
      (withLsCodeLoaded lsmpl (growOneVecU8Spec A)) :=
  growOneVecU8_placed_cl_ok_of_full
    (grow_one_stride_full_placed_of_bs (growOneVecU8_bs_placed_ok_of_fg h_panic hfg))

/-- Block 621 (`RawVec<Vec<u8>>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneVecU8Spec A)`. -/
theorem growOneVecU8_placed_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_621).rebase (blkPl_621).base H)
      (blkPl_621).base
      (withLsCodeLoaded lsmpl (growOneVecU8Spec A)) :=
  growOneVecU8_placed_cl_ok_of_fg h_panic (finish_grow_622_placed_ok hshim halloc hrealloc)

/-- Own-block `blockProgram` contract for block 621 (`growOneVecU8Spec A`). -/
theorem growOneVecU8_blockProgram_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 621 H)
      (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneVecU8Spec A)) := by
  rw [← (instIsLsBlockProg_621 H).eq_blockProgram]
  exact growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc

/-! ## Cross-Block Caller Transfer Lemmas -/

theorem growOneU8_caller_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619) (withLsCodeLoaded lsmpl (growOneU8Spec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (growOneU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneU8_caller_withLsCl_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619) (withLsCl lsmpl (growOneU8Spec A)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (growOneU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneU8_caller_cro_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619) (withLsCodeRoLoaded lsmpl (growOneU8Spec A)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_alloc
    (growOneU8_caller_cl_ok h_panic hshim halloc hrealloc hi)

theorem growOneU8_lscall_blk [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] {m : Memory}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619) (withMemEq m (growOneU8Spec A)) :=
  lscall_blk_cl (callerProg := callerProg)
    (growOneU8_placed_cl_ok h_panic hshim halloc hrealloc) hcl hi (by decide) (by decide)

theorem growOneVecU8_caller_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621) (withLsCodeLoaded lsmpl (growOneVecU8Spec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneVecU8_caller_withLsCl_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8Spec A)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneVecU8_caller_cro_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8Spec A)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_alloc
    (growOneVecU8_caller_cl_ok h_panic hshim halloc hrealloc hi)

theorem growOneVecU8_lscall_blk [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] {m : Memory}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621) (withMemEq m (growOneVecU8Spec A)) :=
  lscall_blk_cl (callerProg := callerProg)
    (growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc) hcl hi (by decide) (by decide)

end SpqrV1.Alloc

end CryptoVerification
