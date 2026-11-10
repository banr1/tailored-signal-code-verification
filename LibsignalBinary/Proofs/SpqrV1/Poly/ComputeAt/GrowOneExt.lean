/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack `RawVec<GF16>::grow_one` Support for `<Poly>::compute_at`

Lifts `finish_grow [local#7]`, `grow_one_gf16_bs_ok_ext`, `grow_one_gf16_full_ok_ext`,
`grow_one_gf16_zero_ok_at`, and `grow_one_gf16_one_ok_at` to `AllocContracts4K`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack allocFailedIn LayoutOk)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt finishGrowStack
  FinishGrowCall panic_at_handle_error_norm_ext allocFailedIn_of_eq
  sessionShimSpec shimName withStack subroutine_ok_withStack_of_subroutine_ok
  rustAllocSpecWithStack rustReallocExternSpecWithStack rustReallocExternWithStack_of_rustRealloc)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K finishGrow8Name memRegion_24
  OptCallInv subroutine_ok_of_withOptInv_none subroutine_ok_withOptInv_none_of
  SepWP.seq_optInv session2ShimSpecWithStack finishGrowSpecWithStack
  finishGrow8ZeroCellsSpecG finishGrow8NeCellsSpecG
  finish_grow_8_zero_cells_opt_of_spec finish_grow_8_ne_cells_opt_of_spec
  stackAt_doReserve_gen growOneStack growOneStrideBsSpec growOneStrideFullSpec
  grow_one_stride_full_of_bs growOneGF16Name growOneGF16BsSpec growOneGF16FullSpec)
open CryptoVerification.SpqrV1.Alloc.GrowOneNorm (
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre)
open CryptoVerification.SpqrV1.Poly.ComputeAt (computeAtName computeAt_fnOff
  growOneGF16ZeroSpec growOneGF16OneSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.GrowOneExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Private 4K `finish_grow [local#7]` Support -/

private theorem shim_ok_opt_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (session2ShimSpecWithStack allocHookStack) none) := by
  refine subroutine_ok_withOptInv_none_of ?_
  have h := subroutine_ok_withStack_of_subroutine_ok (hA.shim_ok_at name k hk) allocHookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionShimSpec allocHookStack).pre x s0 ∗ R := by
    dsimp only [withStack, sessionShimSpec, session2ShimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionShimSpec, session2ShimSpecWithStack] at hpost ⊢
    simpa only [emp_sepConj, sepConj_emp, sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem umulh_stride_eq_zero_4k {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
  rfl

private theorem mul_stride_toNat_4k {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat_4k {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat_4k h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem beq_mul_stride_zero_eq_false_4k {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat_4k h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem hi_stride_eq_false_4k {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]; change align.toNat ≤ 2 ^ 63; omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat_4k (by omega)]
  omega

private def finishGrow8AllocSpecG_4k (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A allocHookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧ x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (allocHookStack + 48) }

private theorem finish_grow_8_zero_opt_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (session2ShimSpecWithStack allocHookStack) none))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (rustAllocSpecWithStack A allocHookStack) none)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (finishGrow8AllocSpecG_4k A) none) := by
  unfold CryptoVerification.SpqrV1.Alloc.Spec.withOptInv finishGrow8AllocSpecG_4k finishGrowSpecWithStack
  simp only [memRegion_24, ProofLib.stackAt_split_cells _ allocHookStack 6 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow8Name) 180
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩; subst cap; subst bs
  have hinv0 : OptCallInv none s0 := trivial
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_4k hlt64
  have hhi := hi_stride_eq_false_4k hbound
  have hcbz := beq_mul_stride_zero_eq_false_4k hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_4k hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)) hinv1
  wp_call hshim (); wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call halloc (new.toNat * stride.toNat, align.toNat); wp_steps
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat_4k hlt64
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0#64; apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 1#64; apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf]; wp_done

private def finishGrow8ReallocSpecG_4k (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A allocHookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (allocHookStack + 48) }

private theorem finish_grow_8_ne_opt_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (rustReallocExternSpecWithStack A allocHookStack) none)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (finishGrow8ReallocSpecG_4k A) none) := by
  unfold CryptoVerification.SpqrV1.Alloc.Spec.withOptInv finishGrow8ReallocSpecG_4k finishGrowSpecWithStack
  simp only [memRegion_24, ProofLib.stackAt_split_cells _ allocHookStack 6 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow8Name) 180
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hcap_ne : cap ≠ 0#64 := ‹_›; have hstr_pos : 0 < stride.toNat := ‹_›
  have hcap_le_new : cap.toNat ≤ new.toNat := ‹_›; have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := ‹_›
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat := Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hold_pos : 0 < cap.toNat * stride.toNat :=
    Nat.mul_pos (Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))) hstr_pos
  have humulh := umulh_stride_eq_zero_4k hlt64; have hhi := hi_stride_eq_false_4k hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_4k hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat_4k hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : LayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨hold_pos, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : OptCallInv none s0 := trivial
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs); wp_steps
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat_4k hlt64
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0#64; apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 1#64; apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]; wp_done

private theorem finish_grow_8_opt_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (finishGrowSpecWithStack A allocHookStack) none) := by
  have hshim := shim_ok_opt_4k hA (name := finishGrow8Name)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name))
    (by rw [(ls_lemma% fnOff finishGrow8Name), (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (rustAllocSpecWithStack A allocHookStack) none) :=
    subroutine_ok_withOptInv_none_of
      (hA.alloc_ok_at _ _ (by rw [(ls_lemma% fnOff finishGrow8Name), (ls_stub% "__rustc::__rust_alloc")]))
  have hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv (rustReallocExternSpecWithStack A allocHookStack) none) :=
    subroutine_ok_withOptInv_none_of
      (rustReallocExternWithStack_of_rustRealloc
        (hA.realloc_ok_at _ _ (by rw [(ls_lemma% fnOff finishGrow8Name), (ls_stub% "__rustc::__rust_realloc")]))
        (by decide) (by decide))
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_opt_ok_4k hshim halloc).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [CryptoVerification.SpqrV1.Alloc.Spec.withOptInv, finishGrowSpecWithStack, finishGrow8AllocSpecG_4k,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_8_ne_opt_ok_4k hrealloc).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [CryptoVerification.SpqrV1.Alloc.Spec.withOptInv, finishGrowSpecWithStack, finishGrow8ReallocSpecG_4k,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

private theorem finish_grow_8_zero_cells_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8ZeroCellsSpecG A allocHookStack) :=
  subroutine_ok_of_withOptInv_none (finish_grow_8_zero_cells_opt_of_spec (finish_grow_8_opt_4k hA))

private theorem finish_grow_8_ne_cells_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8NeCellsSpecG A allocHookStack) :=
  subroutine_ok_of_withOptInv_none (finish_grow_8_ne_cells_opt_of_spec (finish_grow_8_opt_4k hA))

/-! ## `RawVec<GF16>::grow_one` under `AllocContracts4K` -/

private theorem stackAt_growOne_4k (sp : BitVec 64) :
    stackAt sp growOneStack = stackAt (sp - 64#64) finishGrowStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗ ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve_gen sp (by decide)

private theorem grow_new_cap_eq_4k {cap : BitVec 64} (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have h2 : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hsh : cap <<< 1 = BitVec.ofNat 64 (2 * cap.toNat) :=
    BitVec.eq_of_toNat_eq (by rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  by_cases hlt : 4 < 2 * cap.toNat
  · have hult : (4#64).ult (cap <<< 1) = true := by
      rw [BitVec.ult_eq_decide, decide_eq_true_iff, h2]; exact hlt
    rw [hult]; simp only [↓reduceIte, hsh, (by omega : max (2 * cap.toNat) 4 = 2 * cap.toNat)]
  · have hult : (4#64).ult (cap <<< 1) = false := by
      rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, h2]; exact hlt
    rw [hult]; simp only [Bool.false_eq_true, ↓reduceIte, (by omega : max (2 * cap.toNat) 4 = 4)]

theorem grow_one_gf16_bs_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneGF16Name)
      (growOneGF16BsSpec A) := by
  simp only [growOneGF16BsSpec, growOneStrideBsSpec, stackAt_growOne_4k, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff growOneGF16Name)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneGF16Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% growOneGF16Name))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_4k hA
  have hfg1 := finish_grow_8_ne_cells_ok_4k hA
  rw [Program.fnAddr_rel (name := growOneGF16Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% growOneGF16Name))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% growOneGF16Name) 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOneGF16Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq_4k hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (2#64 : BitVec 64).toNat) (2#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 2; omega, hpow, ?_⟩
    change new.toNat * 2 + 2 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 2 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 2 = new.toNat * 2 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% growOneGF16Name))
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
    have hsub_eq : max (2 * cap.toNat) 4 * 2 - bs.length = new.toNat * 2 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 2 = new.toNat * 2 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% growOneGF16Name))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_gf16_full_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneGF16Name)
      (growOneGF16FullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_gf16_bs_ok_ext_4k hA)

/-! ## Call-Site `growOneGF16ZeroSpec` & `growOneGF16OneSpec` Wrappers for `compute_at` -/

private theorem fnAddr_growOneGF16_eq_computeAt_4k (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr growOneGF16Name =
      (tripleRatchetProgAtExt b ext).fnAddr computeAtName +
        bv% (2 ^ 64 +
          ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" -
          ls_off% "<spqr::encoding::polynomial::Poly>::compute_at") := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff growOneGF16Name), computeAt_fnOff]
  bv_omega

private theorem memRegion8_split_16_16_4_4k (p' : BitVec 64) :
    memRegion p' 8 =
      (∃∗ w1 : BitVec 16, ∃∗ w0 : BitVec 16,
        (p' ↦₁₆ w0) ∗ ((p' + 2#64) ↦₁₆ w1) ∗ memRegion (p' + 4#64) 4) := by
  rw [show (8 : Nat) = 2 + (2 + 4) by rfl,
      memRegion_split p' 2 (2 + 4) (by decide),
      memRegion_split (p' + 2#64) 2 4 (by decide),
      ProofLib.memRegion_two p', ProofLib.memRegion_two (p' + 2#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem grow_one_gf16_zero_ok_at_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName +
        bv% (2 ^ 64 +
          ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" -
          ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
      (growOneGF16ZeroSpec A) := by
  rw [← fnAddr_growOneGF16_eq_computeAt_4k b ext]
  refine subroutine_ok_outcome_intro fun v R s0 hpc hrun hpre hsp => ?_
  simp only [growOneGF16ZeroSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  have hpre' : s0.mem ⊨ (growOneGF16FullSpec A).pre (v, 0#64, 2#64, []) s0 ∗ R := by
    simp only [growOneGF16FullSpec, growOneStrideFullSpec, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, by decide, by decide⟩, hmem⟩
  refine (grow_one_gf16_full_ok_ext_4k hA).mono_outcome (v, 0#64, 2#64, []) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec A).post (v, 0#64, 2#64, []) s0 sf ∗ R at hq
    dsimp only [growOneGF16FullSpec, growOneStrideFullSpec, growOneGF16ZeroSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (0#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (0#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h8' : (max (2 * (0#64 : BitVec 64).toNat) 4 - (0#64 : BitVec 64).toNat) * 2 = 8 := rfl
    have h0_2 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    simp only [h4, h8, h8', h0_2, pointsToBytes_nil, BitVec.add_zero, emp_sepConj,
      memRegion8_split_16_16_4_4k, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

private theorem pointsTo16_one_eq_bytes_4k (a : BitVec 64) :
    (a ↦₁₆ 1#16) = (a ↦ₛ [1#8, 0#8]) := by
  simp only [pointsTo16, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_zero]
  rfl

private theorem memRegion6_split_16_4_4k (p' : BitVec 64) :
    memRegion (p' + 2#64) 6 =
      (∃∗ w1 : BitVec 16, ((p' + 2#64) ↦₁₆ w1) ∗ memRegion (p' + 4#64) 4) := by
  rw [show (6 : Nat) = 2 + 4 by rfl,
      memRegion_split (p' + 2#64) 2 4 (by decide),
      ProofLib.memRegion_two (p' + 2#64)]
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]

theorem grow_one_gf16_one_ok_at_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName +
        bv% (2 ^ 64 +
          ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" -
          ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
      (growOneGF16OneSpec A) := by
  rw [← fnAddr_growOneGF16_eq_computeAt_4k b ext]
  refine subroutine_ok_outcome_intro fun ⟨v, p0⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneGF16OneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hp0⟩, hmem⟩
  have hpre' : s0.mem ⊨ (growOneGF16FullSpec A).pre (v, 1#64, p0, [1#8, 0#8]) s0 ∗ R := by
    simp only [growOneGF16FullSpec, growOneStrideFullSpec,
      show (1#64 : BitVec 64) = 0#64 ↔ False by decide, ite_false,
      List.length_cons, List.length_nil, ← pointsTo16_one_eq_bytes_4k,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, hp0, by decide⟩, hmem⟩
  refine (grow_one_gf16_full_ok_ext_4k hA).mono_outcome (v, 1#64, p0, [1#8, 0#8]) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec A).post (v, 1#64, p0, [1#8, 0#8]) s0 sf ∗ R at hq
    dsimp only [growOneGF16FullSpec, growOneStrideFullSpec, growOneGF16OneSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (1#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (1#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h6 : (max (2 * (1#64 : BitVec 64).toNat) 4 - (1#64 : BitVec 64).toNat) * 2 = 6 := rfl
    have hlen2 : BitVec.ofNat 64 ([1#8, 0#8] : List (BitVec 8)).length = 2#64 := rfl
    simp only [h4, h8, h6, hlen2, ← pointsTo16_one_eq_bytes_4k,
      memRegion6_split_16_4_4k, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

end LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.GrowOneExt
