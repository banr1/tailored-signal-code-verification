/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `AllocContracts4K` Contracts for `finish_grow` and `do_reserve_and_handle`

Verifies `RawVecInner::finish_grow [local#2, 4, 8]` and
`RawVecInner::reserve::do_reserve_and_handle [local#2, 4, 7]` under
`AllocContracts4K b A ext` (`allocHookStack = 4096`).
-/

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `AllocContracts4K` Hook Adapters -/

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

/-! ## Arithmetic and Stack Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64} (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]; rfl

private theorem mul_stride_toNat {new stride : BitVec 64} (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64} (h : new.toNat * stride.toNat < 2 ^ 64) :
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

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) : new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]; exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) : new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]; exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) : (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; have ht := congrArg BitVec.toNat heq; change new.toNat = 0 at ht; omega

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat} (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) = stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat} (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) = stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

/-! ## `finish_grow [local#8]` -/

private def finishGrow8AllocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 48) }

private theorem finish_grow_8_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrow8AllocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow8AllocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b (Rust.withPanics ext) hfn (ls_off% finishGrow8Name) 180
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
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)) hinv1
  wp_call hshim (); wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
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

private def finishGrow8ReallocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
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

private theorem finish_grow_8_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrow8ReallocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow8ReallocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b (Rust.withPanics ext) hfn (ls_off% finishGrow8Name) 180
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : OptCallInv img? s0 := by assumption
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat := Nat.mul_le_mul_right stride.toNat hcap_le_new
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
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
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

private theorem finish_grow_8_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_opt_ok hhook hshim halloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8AllocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_8_ne_opt_ok hhook hrealloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8ReallocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-- `finish_grow [local#8]` meets `finishGrowSpec A` under `AllocContracts4K`. -/
theorem finish_grow_8_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrowSpec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_8_opt_ok (hookStack := allocHookStack) (by decide)
      (shim_ok_opt_of_contracts4k hA allocHookStack (by fnoff_eq))
      (alloc_ok_opt_of_contracts4k hA (by fnoff_eq))
      (realloc_ok_opt_of_contracts4k hA (by fnoff_eq)))

/-! ## `finish_grow [local#2]` and `[local#4]` -/

private def finishGrow1AllocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) }

private def finishGrow1ReallocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_2_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow2Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow2Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (Spec.withOptInv (finishGrow1AllocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow2Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b (Rust.withPanics ext) hfn (ls_off% finishGrow2Name) 168
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
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow2Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow2Name)) hinv1
  wp_call hshim (); wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
  wp_call halloc (new.toNat, 1); wp_steps; wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]; wp_done

private theorem finish_grow_2_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow2Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (Spec.withOptInv (finishGrow1ReallocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow2Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b (Rust.withPanics ext) hfn (ls_off% finishGrow2Name) 168
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
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow2Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs); wp_steps; wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]; wp_done

private theorem finish_grow_1_opt_of_zero_ne {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hz : subroutine_ok P addr (Spec.withOptInv (finishGrow1AllocSpecG A hookStack) img?))
    (hne : subroutine_ok P addr (Spec.withOptInv (finishGrow1ReallocSpecG A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine hne.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

/-- `finish_grow [local#2]` meets `finishGrow1Spec A` under `AllocContracts4K`. -/
theorem finish_grow_2_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1Spec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_1_opt_of_zero_ne
      (finish_grow_2_zero_opt_ok (hookStack := allocHookStack) (by decide)
        (shim_ok_opt_of_contracts4k hA allocHookStack (by fnoff_eq))
        (alloc_ok_opt_of_contracts4k hA (by fnoff_eq)))
      (finish_grow_2_ne_opt_ok (hookStack := allocHookStack) (by decide)
        (realloc_ok_opt_of_contracts4k hA (by fnoff_eq))))

private theorem finish_grow_4_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow4Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow4Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (Spec.withOptInv (finishGrow1AllocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow4Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b (Rust.withPanics ext) hfn (ls_off% finishGrow4Name) 168
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
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow4Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow4Name)) hinv1
  wp_call hshim (); wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
  wp_call halloc (new.toNat, 1); wp_steps; wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]; wp_done

private theorem finish_grow_4_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow4Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (Spec.withOptInv (finishGrow1ReallocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow4Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b (Rust.withPanics ext) hfn (ls_off% finishGrow4Name) 168
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
  apply SepWP.seq_optInv (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow4Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs); wp_steps; wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]; wp_done

/-- `finish_grow [local#4]` meets `finishGrow1Spec A` under `AllocContracts4K`. -/
theorem finish_grow_4_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1Spec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_1_opt_of_zero_ne
      (finish_grow_4_zero_opt_ok (hookStack := allocHookStack) (by decide)
        (shim_ok_opt_of_contracts4k hA allocHookStack (by fnoff_eq))
        (alloc_ok_opt_of_contracts4k hA (by fnoff_eq)))
      (finish_grow_4_ne_opt_ok (hookStack := allocHookStack) (by decide)
        (realloc_ok_opt_of_contracts4k hA (by fnoff_eq))))

/-! ## `do_reserve_and_handle [local#7]` -/

private theorem do_reserve_7_stride_raw_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (Spec.withOptInv (doReserveStrideRawSpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [doReserveStrideRawSpecWithStack, stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff doReserve7Name)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := doReserve7Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve7Name))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_8_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := doReserve7Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% doReserve7Name) 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr doReserve7Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hsz_pos : 0 < reserveCapStride stride.toNat cap.toNat len additional * stride.toNat := h.1
  have hpow : ∃ k, align.toNat = 2 ^ k := h.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    h.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact h
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 88#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve7Name))
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
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 88#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve7Name))
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

private theorem do_reserve_7_raw_opt_of_stride {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hs : subroutine_ok P addr (Spec.withOptInv (doReserveStrideRawSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 := by
    refine ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserveStrideRawSpecWithStack A hookStack) img?).pre xs s0 ∗ R := by
    simp only [Spec.withOptInv, doReserveStrideRawSpecWithStack, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  refine hs.mono_outcome xs R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, doReserveStrideRawSpecWithStack, doReserveRawSpecWithStack, xs,
      BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one, and_true]
      at hq ⊢
    exact hq
  · exact Or.inr hfail

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem do_reserve_vec_opt_of_raw {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hraw : subroutine_ok P addr (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserveSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserveSpecWithStack, vecU8At_eq, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [Spec.withOptInv, doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, doReserveRawSpecWithStack, doReserveSpecWithStack, vecU8At_eq]
      at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.withOptInv, doReserveRawSpecWithStack, doReserveSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

/-- `do_reserve_and_handle [local#7]` meets `doReserveStrideRawSpec A` under `AllocContracts4K`. -/
theorem do_reserve_7_stride_raw_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveStrideRawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_7_stride_raw_opt_ok (hookStack := allocHookStack) (by decide)
      (subroutine_ok_withOptInv_none_of (finish_grow_8_ok_ext_4k hA)))

theorem do_reserve_7_raw_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveRawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_7_raw_opt_of_stride
      (subroutine_ok_withOptInv_none_of (do_reserve_7_stride_raw_ok_ext_4k hA)))

/-- `do_reserve_and_handle [local#7]` meets `doReserveSpec A` under `AllocContracts4K`. -/
theorem do_reserve_7_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_vec_opt_of_raw
      (subroutine_ok_withOptInv_none_of (do_reserve_7_raw_ok_ext_4k hA)))

/-! ## `do_reserve_and_handle [local#2]` and `[local#4]` -/

private theorem do_reserve_2_raw32_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [doReserve1Raw32SpecWithStack, stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff doReserve2Name)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := doReserve2Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve2Name))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_24_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_24_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := doReserve2Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]" - ls_off% doReserve2Name))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% doReserve2Name) 120
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr doReserve2Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap); subst hbs
    have hnew_eq0 :
        (if (8#64).ult (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
              s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]" - ls_off% doReserve2Name)) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve2Name))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0; apply SepWPp.of_sepWP_ret; wp_steps; wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by rw [hnew_toNat]
    rw [hsub_eq]; apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]" - ls_off% doReserve2Name)) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve2Name))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0; apply SepWPp.of_sepWP_ret; wp_steps; wp_done

private theorem do_reserve_4_raw32_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [doReserve1Raw32SpecWithStack, stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff doReserve4Name)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := doReserve4Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve4Name))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_24_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_24_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := doReserve4Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]" - ls_off% doReserve4Name))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% doReserve4Name) 120
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr doReserve4Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap); subst hbs
    have hnew_eq0 :
        (if (8#64).ult (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
              s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]" - ls_off% doReserve4Name)) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve4Name))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0; apply SepWPp.of_sepWP_ret; wp_steps; wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by rw [hnew_toNat]
    rw [hsub_eq]; apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]" - ls_off% doReserve4Name)) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve4Name))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0; apply SepWPp.of_sepWP_ret; wp_steps; wp_done

private theorem stackAt_doReserve_eq_32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      memRegion (sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16 ∗
        stackAt sp ((hookStack + 32) + 64) := by
  have heq : (hookStack + 48) + 64 = ((hookStack + 32) + 64) + 16 := by omega
  rw [heq]
  exact ProofLib.stackAt_split_bottom sp ((hookStack + 32) + 64) 16 (by omega)

private theorem do_reserve_raw1_opt_of_raw32 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64)
    (h32 : subroutine_ok P addr (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserve1RawSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserve1RawSpecWithStack, stackAt_doReserve_eq_32_gen _ hhook,
    sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?).pre x s0 ∗
      (btm ∗ R) := by
    simp only [Spec.withOptInv, doReserve1Raw32SpecWithStack, btm, sepConj_assoc]
    ac_nf at hpre ⊢
  refine h32.mono_outcome x (btm ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack,
      stackAt_doReserve_eq_32_gen _ hhook, btm, sepConj_assoc] at hq ⊢
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.withOptInv, doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw_opt_of_raw1 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (h1 : subroutine_ok P addr (Spec.withOptInv (doReserve1RawSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserve1RawSpecWithStack A hookStack) img?).pre x s0 ∗ R := by
    simp only [Spec.withOptInv, doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, hmem⟩
  exact h1.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem do_reserve_2_raw32_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserve1Raw32Spec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_2_raw32_opt_ok (hookStack := allocHookStack) (by decide)
    (subroutine_ok_withOptInv_none_of (finish_grow_2_ok_ext_4k hA)))

theorem do_reserve_4_raw32_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserve1Raw32Spec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_4_raw32_opt_ok (hookStack := allocHookStack) (by decide)
    (subroutine_ok_withOptInv_none_of (finish_grow_4_ok_ext_4k hA)))

theorem do_reserve_2_raw1_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserve1RawSpec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_raw1_opt_of_raw32 (hookStack := allocHookStack) (by decide)
    (subroutine_ok_withOptInv_none_of (do_reserve_2_raw32_ok_ext_4k hA)))

theorem do_reserve_2_raw_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserveRawSpec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_raw_opt_of_raw1
    (subroutine_ok_withOptInv_none_of (do_reserve_2_raw1_ok_ext_4k hA)))

theorem do_reserve_2_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserveSpec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_vec_opt_of_raw
    (subroutine_ok_withOptInv_none_of (do_reserve_2_raw_ok_ext_4k hA)))

theorem do_reserve_4_raw1_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserve1RawSpec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_raw1_opt_of_raw32 (hookStack := allocHookStack) (by decide)
    (subroutine_ok_withOptInv_none_of (do_reserve_4_raw32_ok_ext_4k hA)))

theorem do_reserve_4_raw_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserveRawSpec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_raw_opt_of_raw1
    (subroutine_ok_withOptInv_none_of (do_reserve_4_raw1_ok_ext_4k hA)))

theorem do_reserve_4_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserveSpec A) :=
  subroutine_ok_of_withOptInv_none (do_reserve_vec_opt_of_raw
    (subroutine_ok_withOptInv_none_of (do_reserve_4_raw_ok_ext_4k hA)))

/-! ## `.inImage img` and `doReserveSpecX` Corollaries -/

theorem do_reserve_7_ok_inImage_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name) ((doReserveSpec A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (do_reserve_7_ok_ext_4k hA)

theorem do_reserve_2_ok_inImage_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name) ((doReserveSpec A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (do_reserve_2_ok_ext_4k hA)

theorem do_reserve_4_ok_inImage_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name) ((doReserveSpec A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (do_reserve_4_ok_ext_4k hA)

theorem do_reserve_7_ok_ext_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name) ((doReserveSpecX A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (doReserveSpecX_of_doReserveSpec (do_reserve_7_ok_ext_4k hA))

theorem do_reserve_2_ok_ext_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name) ((doReserveSpecX A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (doReserveSpecX_of_doReserveSpec (do_reserve_2_ok_ext_4k hA))

theorem do_reserve_4_ok_ext_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name) ((doReserveSpecX A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (doReserveSpecX_of_doReserveSpec (do_reserve_4_ok_ext_4k hA))

end CryptoVerification.SpqrV1.Alloc
