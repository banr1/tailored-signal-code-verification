/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.GrowOneSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Sysroot `RawVec::{grow_one, finish_grow}` on `tripleRatchetProgAtExt`

Verifies `finish_grow [liballoc]`, `RawVec<u8>::grow_one`, `finish_grow [libstd]`, and
`RawVec<Vec<u8>>::grow_one` (blocks 619..622) on `tripleRatchetProgAtExt` under
`AllocContracts`, `AllocContracts4K`, and `AllocContractsX`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.CodeLayout
open DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev finishGrowLiballocName : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]"

abbrev finishGrowLibstdName : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]"

gen_decodes libsignalSessionCode_tree spqrSysrootAllocBin [
  (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one" + 92),
  (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]" + 164),
  (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" + 100),
  (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]" + 176)]

/-! ## `AllocContracts4K` Adapters and Stack Helpers -/

private theorem shim_ok_opt_of_contracts4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {name : String} {k : Nat} (hookStack : Nat := allocHookStack)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) none) := by
  refine subroutine_ok_withOptInv_none_of ?_
  have h := subroutine_ok_withStack_of_subroutine_ok (hA.shim_ok_at name k hk) hookStack
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [withStack, sessionShimSpec, noAllocShimSpec, session2ShimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  · dsimp only [withStack, sessionShimSpec, noAllocShimSpec, session2ShimSpecWithStack] at hpost ⊢
    simpa only [emp_sepConj, sepConj_emp, sepConj_assoc] using hpost

private theorem alloc_ok_opt_of_contracts4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (rustAllocSpecWithStack A allocHookStack) none) :=
  subroutine_ok_withOptInv_none_of (hA.alloc_ok_at name k hk)

private theorem realloc_ok_opt_of_contracts4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (rustReallocExternSpecWithStack A allocHookStack) none) :=
  subroutine_ok_withOptInv_none_of
    (rustReallocExternWithStack_of_rustRealloc (hA.realloc_ok_at name k hk)
      (by decide) (by decide))

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
  rw [hdiv]; rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
  BitVec.eq_of_toNat_eq (by rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h])

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq; have ht := congrArg BitVec.toNat heq; rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht; omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]; · simp
    · rw [BitVec.le_def]; change align.toNat ≤ 2 ^ 63; omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]; omega

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]; exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht; omega

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) = stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) = stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

private theorem grow_new_cap_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 4 < 2 * cap.toNat at hc; omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 4 < 2 * cap.toNat at hc
    change 4 = max (2 * cap.toNat) 4; omega

private theorem grow_new_cap_u8_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 8 < 2 ^ 63) :
    (if (8#64).ult (cap <<< 1) = true then cap <<< 1 else 8#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 8) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (8#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 8 < 2 * cap.toNat at hc; omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 8 < 2 * cap.toNat at hc
    change 8 = max (2 * cap.toNat) 8; omega

/-! ## `finish_grow [libstd]` (Generic `stride` and `align`) -/

private def finishGrow8AllocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 48) }

private theorem finish_grow_libstd_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName)
      (Spec.withOptInv (finishGrow8AllocSpecG_sys A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow8AllocSpecG_sys finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")
  code_fetches CryptoVerification.libsignalSessionCode spqrSysrootAllocBin b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]") 180
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩; subst cap; subst bs
  have hinv0 : OptCallInv img? s0 := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")) hinv1
  wp_call hshim (); wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call halloc (new.toNat * stride.toNat, align.toNat); wp_steps; wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat hlt64
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]; wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf]; wp_done

private def finishGrow8ReallocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 48) }

private theorem finish_grow_libstd_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName)
      (Spec.withOptInv (finishGrow8ReallocSpecG_sys A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow8ReallocSpecG_sys finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")
  code_fetches CryptoVerification.libsignalSessionCode spqrSysrootAllocBin b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]") 180
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : OptCallInv img? s0 := by assumption
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : LayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨hold_pos, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs); wp_steps; wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat hlt64
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]; wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]; wp_done

theorem finish_grow_libstd_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName)
      (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_libstd_zero_opt_ok hhook hshim halloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8AllocSpecG_sys,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_libstd_ne_opt_ok hhook hrealloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8ReallocSpecG_sys,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-- `finish_grow [libstd]` meets `finishGrowSpec A` under `AllocContracts`. -/
theorem finish_grow_libstd_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName)
      (finishGrowSpec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_libstd_opt_ok (hookStack := allocHookStack) (by decide)
      (shim_ok_opt_of_contracts hA allocHookStack (by fnoff_eq))
      (alloc_ok_opt_of_contracts hA (by fnoff_eq))
      (realloc_ok_opt_of_contracts hA (by fnoff_eq)))

/-- `finish_grow [libstd]` meets `finishGrowSpec A` under `AllocContracts4K`. -/
theorem finish_grow_libstd_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName)
      (finishGrowSpec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_libstd_opt_ok (hookStack := allocHookStack) (by decide)
      (shim_ok_opt_of_contracts4k hA allocHookStack (by fnoff_eq))
      (alloc_ok_opt_of_contracts4k hA (by fnoff_eq))
      (realloc_ok_opt_of_contracts4k hA (by fnoff_eq)))

/-- `finish_grow [libstd]` meets `(finishGrowSpecX A).inImage img` under `AllocContractsX`. -/
theorem finish_grow_libstd_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowLibstdName)
      ((finishGrowSpecX A).inImage img) :=
  finish_grow_libstd_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (shim_ok_at2_ext_x hA (hk := by fnoff_eq))
    (alloc_ok_at_norm_ext_x hA (hk := by fnoff_eq))
    (realloc_ok_at_norm_ext_x hA (hk := by fnoff_eq))

/-! ## `finish_grow [liballoc]` (`stride = 1, align = 1`) -/

private def finishGrow1AllocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) }

private def finishGrow1ReallocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_liballoc_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName)
      (Spec.withOptInv (finishGrow1AllocSpecG_sys A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1AllocSpecG_sys finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")
  code_fetches CryptoVerification.libsignalSessionCode spqrSysrootAllocBin b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]") 168
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x; dsimp only at *; subst cap; subst bs
  have hinv0 : OptCallInv img? s0 := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")) hinv1
  wp_call hshim (); wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call halloc (new.toNat, 1); wp_steps; wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]; wp_done

private theorem finish_grow_liballoc_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName)
      (Spec.withOptInv (finishGrow1ReallocSpecG_sys A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1ReallocSpecG_sys finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")
  code_fetches CryptoVerification.libsignalSessionCode spqrSysrootAllocBin b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]") 168
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x; dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs); wp_steps; wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]; wp_done

theorem finish_grow_liballoc_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName)
      (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_liballoc_zero_opt_ok hhook hshim halloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow1AllocSpecG_sys,
      FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine (finish_grow_liballoc_ne_opt_ok hhook hrealloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow1ReallocSpecG_sys,
      FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

/-- `finish_grow [liballoc]` meets `finishGrow1Spec A` under `AllocContracts`. -/
theorem finish_grow_liballoc_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName)
      (finishGrow1Spec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_liballoc_opt_ok (hookStack := allocHookStack) (by decide)
      (shim_ok_opt_of_contracts hA allocHookStack (by fnoff_eq))
      (alloc_ok_opt_of_contracts hA (by fnoff_eq))
      (realloc_ok_opt_of_contracts hA (by fnoff_eq)))

/-- `finish_grow [liballoc]` meets `finishGrow1Spec A` under `AllocContracts4K`. -/
theorem finish_grow_liballoc_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName)
      (finishGrow1Spec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_liballoc_opt_ok (hookStack := allocHookStack) (by decide)
      (shim_ok_opt_of_contracts4k hA allocHookStack (by fnoff_eq))
      (alloc_ok_opt_of_contracts4k hA (by fnoff_eq))
      (realloc_ok_opt_of_contracts4k hA (by fnoff_eq)))

/-- `finish_grow [liballoc]` meets `(finishGrow1SpecX A).inImage img` under `AllocContractsX`. -/
theorem finish_grow_liballoc_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowLiballocName)
      ((finishGrow1SpecX A).inImage img) :=
  finish_grow_liballoc_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (shim_ok_at2_ext_x hA (hk := by fnoff_eq))
    (alloc_ok_at_norm_ext_x hA (hk := by fnoff_eq))
    (realloc_ok_at_norm_ext_x hA (hk := by fnoff_eq))

/-! ## `RawVec<u8>::grow_one` -/

/-- Prefix-preserving contract (`bs.length ≤ cap.toNat`) for `RawVec<u8>::grow_one` parameterized by `hookStack`. -/
def growOneU8BsSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 8 < 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 32) + 64)
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗
      (v ↦₆₄ newCapU8 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 8) 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 8 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 32) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem growOneU8_bs_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLiballocName)
      (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneU8Name)
      (Spec.withOptInv (growOneU8BsSpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [growOneU8BsSpecWithStack, newCapU8, stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<u8>>::grow_one")
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneU8Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_24_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_24_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := growOneU8Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]" -
      ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one"))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrSysrootAllocBin b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one") 96
  dsimp only [tripleRatchetProgAtExt, growOneU8Name] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "<alloc::raw_vec::RawVec<u8>>::grow_one" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 8 < 2 ^ 63 := by assumption
  have hnew_eq := grow_new_cap_u8_eq_local hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 8)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 8 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_eq0 : (if (8#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 8#64) = new := hnew_eq
    have hmax_eq : max (2 * 0) 8 = new.toNat := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmax_eq]
    clear hmax_eq
    apply SepWPp.of_sepWP (mid := entry + 52#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]" -
        ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro _
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one"))
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
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : max (2 * cap.toNat) 8 - bs.length = new.toNat - bs.length := by rw [hnew_toNat]
    have hmax_eq : max (2 * cap.toNat) 8 = new.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmax_eq]
    clear hsub_eq hmax_eq
    apply SepWPp.of_sepWP (mid := entry + 52#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]" -
        ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro _
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<alloc::raw_vec::RawVec<u8>>::grow_one"))
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

theorem growOneU8_ok_of_bs {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr (growOneU8BsSpecWithStack A allocHookStack)) :
    subroutine_ok P addr (growOneU8Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12192
  have hstack : stackAt s0.sp extHookStack =
      Frame ∗ stackAt s0.sp ((allocHookStack + 32) + 64) :=
    ProofLib.stackAt_split_bottom s0.sp ((allocHookStack + 32) + 64) 12192 (by decide)
  simp only [growOneU8Spec, BitVec.ofNat_eq_ofNat, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (growOneU8BsSpecWithStack A allocHookStack).pre (x.v, x.cap, x.ptr, x.bs) s0 ∗
        (Frame ∗ R) := by
    simp only [growOneU8BsSpecWithStack, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound⟩, ?_⟩
    rw [hstack] at hmem
    by_cases hcap0 : x.cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hbs.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [growOneU8BsSpecWithStack, growOneU8Spec] at hq ⊢
    rw [hstack]
    simp only [hlen, BitVec.ofNat_eq_ofNat] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    dsimp only [growOneU8BsSpecWithStack, growOneU8Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact False.elim (allowPanic_not_exited hq)
  · exact False.elim (allowPanic_not_exited hq)

/-- `RawVec<u8>::grow_one` meets `growOneU8Spec A` under `AllocContracts`. -/
theorem growOneU8_sysroot_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneU8Name)
      (growOneU8Spec A) :=
  growOneU8_ok_of_bs
    (subroutine_ok_of_withOptInv_none
      (growOneU8_bs_opt_ok (hookStack := allocHookStack) (by decide)
        (subroutine_ok_withOptInv_none_of (finish_grow_liballoc_ok_ext hA))))

theorem growOneU8_sysroot_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneU8Name) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (growOneU8Spec A) := by
  rw [← Program.fnAddr_rel (P := libsignalSessionCode) rfl rfl hk]
  exact growOneU8_sysroot_ok_ext hA

/-- `RawVec<u8>::grow_one` meets `growOneU8Spec A` under `AllocContracts4K`. -/
theorem growOneU8_sysroot_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneU8Name)
      (growOneU8Spec A) :=
  growOneU8_ok_of_bs
    (subroutine_ok_of_withOptInv_none
      (growOneU8_bs_opt_ok (hookStack := allocHookStack) (by decide)
        (subroutine_ok_withOptInv_none_of (finish_grow_liballoc_ok_ext_4k hA))))

theorem growOneU8_sysroot_ok_at_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneU8Name) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (growOneU8Spec A) := by
  rw [← Program.fnAddr_rel (P := libsignalSessionCode) rfl rfl hk]
  exact growOneU8_sysroot_ok_ext_4k hA

/-! ## `RawVec<Vec<u8>>::grow_one` -/

/-- Prefix-preserving contract (`bs.length ≤ cap.toNat * 24`) for `RawVec<Vec<u8>>::grow_one` parameterized by `hookStack`. -/
def growOneVecU8BsSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 24 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 24) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 24 - bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 24 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 48) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem growOneVecU8_bs_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowLibstdName)
      (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneVecU8Name)
      (Spec.withOptInv (growOneVecU8BsSpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [growOneVecU8BsSpecWithStack, stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneVecU8Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_8_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := growOneVecU8Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]" -
      ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one"))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrSysrootAllocBin b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one") 104
  dsimp only [tripleRatchetProgAtExt, growOneVecU8Name] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * 24 := by assumption
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
    clear hmul_eq
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]" -
        ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro _
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 24#64, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one"))
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
    clear hsub_eq hmul_eq
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]" -
        ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro _
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 8#64, 24#64, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one"))
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

theorem growOneVecU8_ok_of_full {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfull : subroutine_ok P addr (growOneStrideFullSpec A 24 8)) :
    subroutine_ok P addr (growOneVecU8Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12176
  have hstack : stackAt s0.sp extHookStack = Frame ∗ stackAt s0.sp growOneStack :=
    ProofLib.stackAt_split_bottom s0.sp growOneStack 12176 (by decide)
  simp only [growOneVecU8Spec, BitVec.ofNat_eq_ofNat, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (growOneStrideFullSpec A 24 8).pre (x.v, x.cap, x.ptr, x.bs) s0 ∗ (Frame ∗ R) := by
    simp only [growOneStrideFullSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hptr, hbound⟩, ?_⟩
    rw [hstack] at hmem
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hfull.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [growOneStrideFullSpec, growOneVecU8Spec, newCapVecU8] at hq ⊢
    rw [hstack]
    simp only [BitVec.ofNat_eq_ofNat] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    dsimp only [growOneStrideFullSpec, growOneVecU8Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact False.elim (allowPanic_not_exited hq)
  · exact False.elim (allowPanic_not_exited hq)

/-- `RawVec<Vec<u8>>::grow_one` meets `growOneVecU8Spec A` under `AllocContracts`. -/
theorem growOneVecU8_sysroot_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A) :=
  growOneVecU8_ok_of_full
    (grow_one_stride_full_of_bs
      (subroutine_ok_of_withOptInv_none
        (growOneVecU8_bs_opt_ok (hookStack := allocHookStack) (by decide)
          (subroutine_ok_withOptInv_none_of (finish_grow_libstd_ok_ext hA)))))

theorem growOneVecU8_sysroot_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneVecU8Name) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (growOneVecU8Spec A) := by
  rw [← Program.fnAddr_rel (P := libsignalSessionCode) rfl rfl hk]
  exact growOneVecU8_sysroot_ok_ext hA

/-- `RawVec<Vec<u8>>::grow_one` meets `growOneVecU8Spec A` under `AllocContracts4K`. -/
theorem growOneVecU8_sysroot_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A) :=
  growOneVecU8_ok_of_full
    (grow_one_stride_full_of_bs
      (subroutine_ok_of_withOptInv_none
        (growOneVecU8_bs_opt_ok (hookStack := allocHookStack) (by decide)
          (subroutine_ok_withOptInv_none_of (finish_grow_libstd_ok_ext_4k hA)))))

theorem growOneVecU8_sysroot_ok_at_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneVecU8Name) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (growOneVecU8Spec A) := by
  rw [← Program.fnAddr_rel (P := libsignalSessionCode) rfl rfl hk]
  exact growOneVecU8_sysroot_ok_ext_4k hA

/-! ## 32 KiB Stack Entrypoint (`growOneVecU8Stack32kSpec`) -/

/-- `growOneVecU8Spec A` lifted to a 32 KiB caller stack (`serializeSubStackX`). -/
def growOneVecU8Stack32kSpec (A : RustAlloc) : Spec GrowOneCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * 24 ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 8 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool ∗ stackAt s.sp 32768
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (x.v ↦₆₄ newCapVecU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24)) ∗
      A.pool ∗ stackAt s0.sp 32768
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem growOneVecU8_sysroot_stack32k_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      ((growOneVecU8Stack32kSpec A).inImage img) := by
  have hbs : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      ((growOneVecU8BsSpecWithStack A extHookStack).inImage img) :=
    growOneVecU8_bs_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := extHookStack) (img? := some img) (by decide)
      (finish_grow_libstd_ok_ext_xa hA)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 32768#64) 16272
  have hstack : stackAt s0.sp 32768 =
      Frame ∗ stackAt s0.sp ((extHookStack + 48) + 64) :=
    ProofLib.stackAt_split_bottom s0.sp ((extHookStack + 48) + 64) 16272 (by decide)
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (growOneVecU8Stack32kSpec A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre0⟩
  simp only [growOneVecU8Stack32kSpec, BitVec.ofNat_eq_ofNat, sepConj_assoc,
    satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨
      ((growOneVecU8BsSpecWithStack A extHookStack).inImage img).pre
        (x.v, x.cap, x.ptr, x.bs) s0 ∗ (Frame ∗ R) := by
    change s0.mem ⊨
      (⌜ImgCallInv img s0⌝ ∗
        (growOneVecU8BsSpecWithStack A extHookStack).pre (x.v, x.cap, x.ptr, x.bs) s0) ∗
        (Frame ∗ R)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    simp only [growOneVecU8BsSpecWithStack, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound⟩, ?_⟩
    rw [hstack] at hmem
    by_cases hcap0 : x.cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hbs.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hsub_mul : (max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24 =
        max (2 * x.cap.toNat) 4 * 24 - x.bs.length := by
      rw [Nat.sub_mul, hlen]
    dsimp only [Spec.inImage, growOneVecU8BsSpecWithStack, growOneVecU8Stack32kSpec,
      newCapVecU8] at hq ⊢
    rw [hstack, hsub_mul]
    simp only [BitVec.ofNat_eq_ofNat] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    dsimp only [Spec.inImage, growOneVecU8BsSpecWithStack, growOneVecU8Stack32kSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact False.elim (allowPanic_not_exited hq)
  · exact False.elim (allowPanic_not_exited hq)

theorem growOneVecU8_sysroot_stack32k_ok_at_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff growOneVecU8Name) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((growOneVecU8Stack32kSpec A).inImage img) := by
  rw [← Program.fnAddr_rel (P := libsignalSessionCode) rfl rfl hk]
  exact growOneVecU8_sysroot_stack32k_ok_ext_xa hA

end CryptoVerification.SpqrV1.Alloc
