/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# `<alloc::raw_vec::RawVecInner>::finish_grow` (`0x15de4`)

Verifies `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (`0x15de4`, 45 instructions)
against the unified `finishGrowSpec A` contract on `tripleRatchetProgAt`, covering both `cap = 0` (`__rust_alloc`)
and `cap ≠ 0` (`__rust_realloc`) and generic `(stride, align)` (`(1, 1)`, `(104, 8)`, `(72, 8)`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic and memory helpers for generic `stride` and `align` -/

theorem umulh_stride_eq_zero_shared_lb {new stride : BitVec 64}
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

private abbrev umulh_stride_eq_zero := @umulh_stride_eq_zero_shared_lb

theorem mul_stride_toNat_shared_lb {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private abbrev mul_stride_toNat := @mul_stride_toNat_shared_lb

theorem mul_stride_eq_ofNat_shared_lb {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private abbrev mul_stride_eq_ofNat := @mul_stride_eq_ofNat_shared_lb

theorem mul_stride_ne_zero_shared_lb {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private abbrev mul_stride_ne_zero := @mul_stride_ne_zero_shared_lb

theorem beq_mul_stride_zero_eq_false_shared_lb {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private abbrev beq_mul_stride_zero_eq_false := @beq_mul_stride_zero_eq_false_shared_lb

theorem hi_stride_eq_false_shared_lb {new stride align : BitVec 64}
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

private abbrev hi_stride_eq_false := @hi_stride_eq_false_shared_lb

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrow_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

/-! ## Case 1: `cap = 0` (`__rust_alloc`) -/

def finishGrowAllocSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 48) }

theorem finish_grow_zero_ok_of_hooks_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustAllocSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowAllocSpecWithStack A hookStack)) := by
  unfold specWithOptInv finishGrowAllocSpecWithStack finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowName = num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.libsignalSessionBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  subst cap
  subst bs
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
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

/-! ## Case 2: `cap ≠ 0` (`__rust_realloc`) -/

def finishGrowReallocSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
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

theorem finish_grow_ne_ok_of_hooks_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustReallocExternSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowReallocSpecWithStack A hookStack)) := by
  unfold specWithOptInv finishGrowReallocSpecWithStack finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowName = num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.libsignalSessionBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : OptCallInv oimg s0 := by assumption
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
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
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

/-! ## Unified `finish_grow_ok` theorems -/

theorem finish_grow_ok_of_hooks_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustAllocSpecWithStack A hookStack)))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustReallocExternSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack A hookStack)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_ok_of_hooks_opt hstack hshim halloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrowAllocSpecWithStack,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_ne_ok_of_hooks_opt hstack hrealloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrowReallocSpecWithStack,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

theorem finish_grow_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec A) :=
  subroutine_ok_of_optNone <|
    finish_grow_ok_of_hooks_opt (by decide)
      (shim_opt_of_base hA (name := finishGrowName)
        (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (alloc_opt_of_base hA (name := finishGrowName)
        (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (realloc_opt_of_base hA (name := finishGrowName)
        (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))

theorem finish_grow_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr finishGrowName)
      (finishGrowSpec A) :=
  finish_grow_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (`0x15de4`) meets `finishGrowSpec A`
on `tripleRatchetProgAt`. -/
theorem finish_grow_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr finishGrowName)
      (finishGrowSpec A) :=
  subroutine_ok_kit_of_trTrap (finish_grow_ok_trap hA)

theorem finish_grow_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowName)
      ((finishGrowSpecX A).inImage img) :=
  finish_grow_ok_of_hooks_opt (oimg := some img) (by decide)
    (shim_opt_of_x hA (name := finishGrowName)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
    (alloc_opt_of_x hA (name := finishGrowName)
      (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
    (realloc_opt_of_x hA (name := finishGrowName)
      (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))

/-! ## Relocatable Per-Block Proofs (`[LibsignalPlacement]`, Block `45`) -/

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h'.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

theorem finish_grow_zero_placed_ok_of_hooks_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowAllocSpecWithStack A hookStack) := by
  unfold finishGrowAllocSpecWithStack finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left, sepExists_sepConj_right]
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

theorem finish_grow_ne_placed_ok_of_hooks_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowReallocSpecWithStack A hookStack) := by
  unfold finishGrowReallocSpecWithStack finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left, sepExists_sepConj_right]
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

theorem finish_grow_placed_ok_of_hooks_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_placed_ok_of_hooks_opt hstack hshim halloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrowAllocSpecWithStack,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_ne_placed_ok_of_hooks_opt hstack hrealloc).mono_outcome
      x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrowReallocSpecWithStack,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-- Relocatable `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (Block `45`) meets
`finishGrowSpec A`. -/
theorem finish_grow_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpec A) :=
  finish_grow_placed_ok_of_hooks_opt (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    (rustReallocExternWithStack_of_rustRealloc (ls_hook_ok_of_mem hrealloc) (by decide) (by decide))

theorem finish_grow_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecX A) :=
  finish_grow_placed_ok_of_hooks_opt (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (ls_hook_ok_of_mem hrealloc) (by decide) (by decide))

end CryptoVerification.LibsignalTripleRatchet
