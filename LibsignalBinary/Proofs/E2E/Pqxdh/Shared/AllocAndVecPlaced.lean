/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVec
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable Per-Block Proofs for `AllocAndVec`

Proves relocatable contracts for unmutated Block `588`
(`<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]`, `[LibsignalPlacement]`) and mutated
Block `55` (`<alloc::vec::Vec<u8>>::append_elements`, `[LibsignalFullPlacement]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic and Memory Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
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

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_tryAllocateIn (sp : BitVec 64) :
    stackAt sp finishGrowStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 4096 6 (by decide)

private theorem hi_append_eq_false {cap len n : Nat}
    (hle : len + n ≤ cap) (hcap : cap < 2 ^ 64) :
    (BitVec.ofNat 64 cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 n) = false := by
  have hlen : len < 2 ^ 64 := by omega
  have hn : n < 2 ^ 64 := by omega
  have hsub : (BitVec.ofNat 64 cap - BitVec.ofNat 64 len).toNat = cap - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hlen]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hlen]
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  omega

private theorem ofNat_beq_zero_eq_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-! ## Block `588`: `RawVecInner::try_allocate_in` (`[LibsignalPlacement]`) -/

/-- Relocatable `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (Block `588`, unmutated)
meets `tryAllocateInSpec A` under `[LibsignalPlacement]`. -/
theorem tryAllocateIn2_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (blkPl_588).base
      (tryAllocateInSpec A) := by
  unfold tryAllocateInSpec
  simp only [memRegion_24, stackAt_tryAllocateIn, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_any hshim
  have halloc' : subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_any halloc
  dsimp only [noAllocShimSpec] at hshim'
  wp_init x s0
  obtain ⟨out, new, align, stride⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (new.toNat * stride.toNat, align.toNat)
  wp_steps
  wp_if hoom
  · have hoom0 : sf_1.readReg64 Reg.x0 = 0 := hoom
    simp only [hoom0, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 0#64
    simp only [ite_true]
    wp_done
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done

theorem tryAllocateIn2_placed_ok_cl [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 588) (withLsCodeLoaded lsmpl (tryAllocateInSpec A)) :=
  ls_subroutine_ok_of_block (j := 588)
    (subroutine_ok_withLsCodeLoaded_of_plain (tryAllocateIn2_placed_ok hshim halloc)) hi

/-! ## Block `55`: `Vec<u8>::append_elements` (`[LibsignalFullPlacement]`) -/

/-- Relocatable fast-path `<alloc::vec::Vec<u8>>::append_elements` (`128 + 32 ≤ 192`, Block `55`)
meets `pqxdhVecAppendElementsFastSpec` under `[LibsignalFullPlacement]`. -/
theorem vecAppendElements_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (blkPl_55).base
      pqxdhVecAppendElementsFastSpec := by
  unfold pqxdhVecAppendElementsFastSpec
  cells_unfold
  have hmemcpy' : subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec := ls_hook_ok_any hmemcpy
  dsimp only [framelessMemcpySpec] at hmemcpy'
  wp_init x s0
  obtain ⟨vecHdr, vecPtr, srcPtr, bs⟩ := x
  dsimp only at *
  subst h_1 h_2
  wp_steps
  rw [← h]
  wp_call hmemcpy' (vecPtr + 128#64, s0.readReg64 (.gpr 1#5), bs)
  simp only [h] at *
  wp_steps
  wp_done

theorem vecAppendElements_fast_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec) :=
  full_ls_subroutine_ok_of_plain (j := 55) (vecAppendElements_fast_placed_ok hmemcpy)

/-- Relocatable general fast-path `<alloc::vec::Vec<u8>>::append_elements` (`len + bs.length ≤ cap`,
Block `55`) meets `vecAppendElementsGenFastSpec` under `[LibsignalFullPlacement]`. -/
theorem vecAppendElements_gen_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (blkPl_55).base
      vecAppendElementsGenFastSpec := by
  unfold vecAppendElementsGenFastSpec
  cells_unfold
  have hmemcpy' : subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec := ls_hook_ok_any hmemcpy
  dsimp only [framelessMemcpySpec] at hmemcpy'
  wp_init x s0
  obtain ⟨vecHdr, vecPtr, srcPtr, cap, len, bs⟩ := x
  dsimp only at *
  have hle : len + bs.length ≤ cap := ‹len + bs.length ≤ cap›
  have hcap : cap < 2 ^ 64 := ‹cap < 2 ^ 64›
  have hhi := hi_append_eq_false hle hcap
  cases bs with
  | nil =>
    simp only [List.length_nil, Nat.add_zero,
      memRegion_zero, pointsToBytes_nil] at *
    wp_steps
    wp_done
  | cons b0 bs' =>
    have hpos : 0 < (b0 :: bs').length := by simp
    have hlt : (b0 :: bs').length < 2 ^ 64 := by omega
    have hcbz := ofNat_beq_zero_eq_false hpos hlt
    wp_steps
    wp_call hmemcpy' (vecPtr + BitVec.ofNat 64 len, s0.readReg64 (.gpr 1#5), b0 :: bs')
    wp_steps
    wp_done

abbrev vecAppendElements1_gen_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :=
  vecAppendElements_gen_fast_placed_ok hmemcpy

abbrev vecAppendElements2_gen_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :=
  vecAppendElements_gen_fast_placed_ok hmemcpy

theorem vecAppendElements_gen_fast_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl vecAppendElementsGenFastSpec) :=
  full_ls_subroutine_ok_of_plain (j := 55) (vecAppendElements_gen_fast_placed_ok hmemcpy)

end CryptoVerification.E2E.Pqxdh.Shared
