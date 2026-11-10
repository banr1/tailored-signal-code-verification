/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `AllocContracts4K` Contracts for `<VecDeque<spqr::chain::ChainEpoch>>::grow`

Verifies `RawVec<ChainEpoch>::grow_one` and `<VecDeque<ChainEpoch>>::grow`
(`ChainProofs.vecDequeGrowSpec`, `ChainProofs.VecDequeGrowOkX`) under
`AllocContracts4K` (`allocHookStack = 4096`).
-/

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open GrowOneNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 4 KiB `finish_grow [local#8]` Support -/

private theorem shim_ok_opt_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (session2ShimSpecWithStack allocHookStack) none) := by
  refine subroutine_ok_withOptInv_none_of ?_
  have h := subroutine_ok_withStack_of_subroutine_ok (hA.shim_ok_at name k hk) allocHookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionShimSpec allocHookStack).pre x s0 ∗ R := by
    dsimp only [withStack, sessionShimSpec, noAllocShimSpec, session2ShimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionShimSpec, noAllocShimSpec, session2ShimSpecWithStack] at hpost ⊢
    simpa only [emp_sepConj, sepConj_emp, sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem umulh_stride_eq_zero' {new stride : BitVec 64} (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]; rfl

private theorem mul_stride_toNat' {new stride : BitVec 64} (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat' {new stride : BitVec 64} (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq; rw [mul_stride_toNat' h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem beq_mul_stride_zero_eq_false' {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat' h] at ht; change new.toNat * stride.toNat = 0 at ht; omega

private theorem hi_stride_eq_false' {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]; · simp
    · rw [BitVec.le_def]; change align.toNat ≤ 2 ^ 63; omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat' (by omega)]; omega

private def finishGrow8AllocSpecG' (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A allocHookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧ x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (allocHookStack + 48) }

private theorem finish_grow_8_zero_opt_ok' {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (session2ShimSpecWithStack allocHookStack) none))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A allocHookStack) none)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrow8AllocSpecG' A) none) := by
  unfold Spec.withOptInv finishGrow8AllocSpecG' finishGrowSpecWithStack
  simp only [memRegion_24, ProofLib.stackAt_split_cells _ allocHookStack 6 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow8Name) 180
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩; subst cap; subst bs
  have hinv0 : OptCallInv none s0 := trivial
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero' hlt64
  have hhi := hi_stride_eq_false' hbound
  have hcbz := beq_mul_stride_zero_eq_false' hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat' hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)) hinv1
  wp_call hshim (); wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call halloc (new.toNat * stride.toNat, align.toNat); wp_steps
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat' hlt64
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf]; wp_done

private def finishGrow8ReallocSpecG' (A : RustAlloc) : Spec FinishGrowCall :=
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

private theorem finish_grow_8_ne_opt_ok' {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A allocHookStack) none)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrow8ReallocSpecG' A) none) := by
  unfold Spec.withOptInv finishGrow8ReallocSpecG' finishGrowSpecWithStack
  simp only [memRegion_24, ProofLib.stackAt_split_cells _ allocHookStack 6 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
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
  have humulh := umulh_stride_eq_zero' hlt64; have hhi := hi_stride_eq_false' hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat' hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat' hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : LayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨hold_pos, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : OptCallInv none s0 := trivial
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)) hinv0
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro _
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs); wp_steps
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := mul_stride_eq_ofNat' hlt64
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]; wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]; wp_done

private theorem finish_grow_8_opt_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrowSpecWithStack A allocHookStack) none) := by
  have hshim := shim_ok_opt_4k hA (name := finishGrow8Name)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)) (by fnoff_eq)
  have halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A allocHookStack) none) :=
    subroutine_ok_withOptInv_none_of (hA.alloc_ok_at _ _ (by fnoff_eq))
  have hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A allocHookStack) none) :=
    subroutine_ok_withOptInv_none_of
      (rustReallocExternWithStack_of_rustRealloc (hA.realloc_ok_at _ _ (by fnoff_eq)) (by decide) (by decide))
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_opt_ok' hshim halloc).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8AllocSpecG',
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_8_ne_opt_ok' hrealloc).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8ReallocSpecG',
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-! ## Cell-Unfolded `finish_grow [local#8]` and `RawVec<ChainEpoch>::grow_one` -/

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

private theorem stackAt_growOne4k (sp : BitVec 64) :
    stackAt sp growOneStack = stackAt (sp - 64#64) finishGrowStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗ ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve_gen sp (by decide)

private theorem grow_new_cap_eq4k {cap : BitVec 64} (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have h2 : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hsh : cap <<< 1 = BitVec.ofNat 64 (2 * cap.toNat) :=
    BitVec.eq_of_toNat_eq (by rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  by_cases hlt : 4 < 2 * cap.toNat
  · have hult : (4#64).ult (cap <<< 1) = true := by rw [BitVec.ult_eq_decide, decide_eq_true_iff, h2]; exact hlt
    rw [hult]; simp only [↓reduceIte, hsh, (by omega : max (2 * cap.toNat) 4 = 2 * cap.toNat)]
  · have hult : (4#64).ult (cap <<< 1) = false := by rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, h2]; exact hlt
    rw [hult]; simp only [Bool.false_eq_true, ↓reduceIte, (by omega : max (2 * cap.toNat) 4 = 4)]

/-- `RawVec<ChainEpoch>::grow_one` meets `growOneChainEpochBsSpec A` under `AllocContracts4K`. -/
theorem grow_one_chain_epoch_bs_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
      (growOneChainEpochBsSpec A) := by
  simp only [growOneChainEpochBsSpec, growOneStrideBsSpec, stackAt_growOne4k, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff growOneChainEpochName)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneChainEpochName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% growOneChainEpochName))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_4k hA
  have hfg1 := finish_grow_8_ne_cells_ok_4k hA
  rw [Program.fnAddr_rel (name := growOneChainEpochName)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% growOneChainEpochName))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% growOneChainEpochName) 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOneChainEpochName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq4k hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (112#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 112; omega, hpow, ?_⟩
    change new.toNat * 112 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 112 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 112 = new.toNat * 112 := by rw [hnew_toNat]; rfl
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
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% growOneChainEpochName))
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
    have hsub_eq : max (2 * cap.toNat) 4 * 112 - bs.length = new.toNat * 112 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 112 = new.toNat * 112 := by
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
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% growOneChainEpochName))
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

theorem grow_one_chain_epoch_full_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
      (growOneChainEpochFullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_chain_epoch_bs_ok_ext_4k hA)

theorem grow_one_chain_epoch_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
      (growOneChainEpochSpec A) :=
  grow_one_stride_empty_of_bs (grow_one_chain_epoch_bs_ok_ext_4k hA)

/-! ## `<VecDeque<ChainEpoch>>::grow` Branch Contracts -/

private theorem stackAt_vecDequeGrow4k (sp : BitVec 64) :
    stackAt sp vecDequeGrowStack =
      stackAt (sp - 32#64) growOneStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4208 4 (by decide)
  change stackAt sp vecDequeGrowStack =
    stackAt (sp - 32#64) growOneStack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]

private theorem stackAt_vecDequeGrow_pack (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) growOneStack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    stackAt sp vecDequeGrowStack := by
  rw [stackAt_vecDequeGrow4k sp]
  have hcells :
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    refine Entails.trans ?_ (Entails.sepExists_intro (P := fun w0 => ∃∗ w1, ∃∗ w2, ∃∗ w3,
      ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗ ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) v0)
    refine Entails.trans ?_ (Entails.sepExists_intro (P := fun w1 => ∃∗ w2, ∃∗ w3,
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗ ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) v1)
    refine Entails.trans ?_ (Entails.sepExists_intro (P := fun w2 => ∃∗ w3,
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗ ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) v2)
    exact Entails.sepExists_intro (P := fun w3 =>
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ w3)) v3
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right hcells)

private theorem vec_deque_nonwrap_ule4k {cap head len : BitVec 64}
    (h : head.toNat + len.toNat ≤ cap.toNat) :
    head.ule (cap - len) = true := by
  have hle : len.toNat ≤ cap.toNat := by omega
  rw [BitVec.ule_eq_decide, decide_eq_true_iff, BitVec.toNat_sub_of_le hle]
  omega

/-- `VecDeque<ChainEpoch>::grow` meets `vecDequeGrowNonwrapBsSpec A` under `AllocContracts4K`. -/
theorem vec_deque_grow_nonwrap_bs_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowNonwrapBsSpec A) := by
  simp only [vecDequeGrowNonwrapBsSpec, stackAt_vecDequeGrow4k, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff vecDequeGrowName)
  have hgrow := grow_one_chain_epoch_bs_ok_ext_4k hA
  rw [Program.fnAddr_rel (name := vecDequeGrowName)
    hfn (ls_lemma% fnOff growOneChainEpochName)
    (k := num% (ls_off% growOneChainEpochName - ls_off% vecDequeGrowName))
    (by decide)] at hgrow
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% vecDequeGrowName) 152
  dsimp only [tripleRatchetProgAtExt] at hgrow ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr vecDequeGrowName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, len, bs⟩ := x
  dsimp only at *
  have hule := vec_deque_nonwrap_ule4k (cap := cap) (head := head) (len := len) (by omega)
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_off% growOneChainEpochName - ls_off% vecDequeGrowName))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ len) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hgrow
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], ‹_›, ‹_›, by change max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63; omega⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

theorem vec_deque_grow_empty_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowEmptySpec A) := by
  have h := vec_deque_grow_nonwrap_bs_ok_ext_4k hA
  refine subroutine_ok_outcome_intro fun ⟨d, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (vecDequeGrowNonwrapBsSpec A).pre (d, 0#64, ptr, 0#64, 0#64, []) s0 ∗ R := by
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      List.length_nil, Nat.le_refl, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, trivial, hpre.1.2, trivial, by decide⟩, hpre.2⟩
  refine h.mono_outcome (d, 0#64, ptr, 0#64, 0#64, []) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have h0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec, h0,
      Nat.sub_zero, List.length_nil, BitVec.add_zero, pointsToBytes_nil, emp_sepConj,
      sepExists_sepConj_left, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact hpost
  · exact Or.inr hfail

private theorem vec_deque_wrap_ule_false4k {cap head : BitVec 64}
    (h : 0 < head.toNat) :
    head.ule (cap - cap) = false := by
  rw [BitVec.sub_self, BitVec.ule_eq_decide, decide_eq_false_iff_not]
  change ¬ (head.toNat ≤ 0)
  omega

private theorem vec_deque_memcpy_branch4k {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat) (h2 : head.toNat < cap.toNat - head.toNat) :
    (cap - head).ule head = false := by
  have hsub1 : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, hsub1]
  omega

private theorem vec_deque_memcpy_fit4k {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat)
    (hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63) :
    (BitVec.ofNat 64 (max (2 * cap.toNat) 4) - cap).ult head = false := by
  have hnc : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle : cap ≤ BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
    rw [BitVec.le_def, hnc]; omega
  have hsub1 : (BitVec.ofNat 64 (max (2 * cap.toNat) 4) - cap).toNat =
      max (2 * cap.toNat) 4 - cap.toNat := by
    rw [BitVec.toNat_sub_of_le hle, hnc]
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub1]
  omega

private theorem vec_deque_memmove_branch4k {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat) (h2 : cap.toNat - head.toNat ≤ head.toNat) :
    (cap - head).ule head = true := by
  have hsub1 : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  rw [BitVec.ule_eq_decide, decide_eq_true_iff, hsub1]
  omega

private theorem shift_128_sub_16_toNat4k {x : BitVec 64} (h : x.toNat * 128 < 2 ^ 64) :
    (x <<< 7 - x <<< 4).toNat = x.toNat * 112 := by
  have h7 : (x <<< 7).toNat = x.toNat * 128 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have h4 : (x <<< 4).toNat = x.toNat * 16 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hle : x <<< 4 ≤ x <<< 7 := by
    rw [BitVec.le_def, h4, h7]; omega
  rw [BitVec.toNat_sub_of_le hle, h7, h4]
  omega

private theorem listMove_append_to_end4k {bs1 bs2 : List (BitVec 8)} :
    listMove (bs1 ++ bs2) bs2.length 0 bs1.length =
      (bs1 ++ bs2).take bs2.length ++ bs1 := by
  unfold listMove
  have hdrop0 : (bs1 ++ bs2).drop 0 = bs1 ++ bs2 := rfl
  have htake1 : (bs1 ++ bs2).take bs1.length = bs1 := by
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop_end : (bs1 ++ bs2).drop (bs2.length + bs1.length) = [] := by
    rw [Nat.add_comm, ← List.length_append, List.drop_length]
  rw [hdrop0, htake1, hdrop_end, List.append_nil]

private theorem pointsToBytes_listMove_append_entails4k (base : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) :
    (base ↦ₛ listMove (bs1 ++ bs2) bs2.length 0 bs1.length) ⊢
      memRegion base bs2.length ∗ ((base + BitVec.ofNat 64 bs2.length) ↦ₛ bs1) := by
  rw [listMove_append_to_end4k, pointsToBytes_append]
  have hlen : ((bs1 ++ bs2).take bs2.length).length = bs2.length :=
    List.length_take_of_le (by rw [List.length_append]; omega)
  rw [hlen]
  apply sepConj_mono_left
  have hreg := pointsToBytes_entails_memRegion base ((bs1 ++ bs2).take bs2.length)
  rwa [hlen] at hreg

private theorem madd_112_eq4k (p x : BitVec 64) (_h : x.toNat * 112 < 2 ^ 64) :
    p + x * 112#64 = p + BitVec.ofNat 64 (x.toNat * 112) := by
  have hx : x * 112#64 = BitVec.ofNat 64 (x.toNat * 112) := by
    apply BitVec.eq_of_toNat_eq
    have h112 : (112#64 : BitVec 64).toNat = 112 := rfl
    rw [BitVec.toNat_mul, h112, BitVec.toNat_ofNat]
  rw [hx]

private def sessionMemmoveFrontToEndSpec4K (hookStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (base, bs_front, uninitLen) s0 =>
    ⌜s0.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧
      s0.readReg64 .x1 = base ∧
      (s0.readReg64 .x2).toNat = bs_front.length ∧
      uninitLen ≤ 2 ^ 64⌝ ∗
      (base ↦ₛ bs_front) ∗
      memRegion (base + BitVec.ofNat 64 bs_front.length) uninitLen ∗
      stackAt s0.sp hookStack
  post := fun (base, bs_front, uninitLen) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧ sf.trace = s0.trace⌝ ∗
      memRegion base uninitLen ∗
      ((base + BitVec.ofNat 64 uninitLen) ↦ₛ bs_front) ∗
      stackAt s0.sp hookStack

private theorem session_memmove_front_to_end_ok4k {prog : Program} {addr : BitVec 64}
    {hookStack : Nat} (hmm : subroutine_ok prog addr (sessionMemmoveSpec hookStack)) :
    subroutine_ok prog addr (sessionMemmoveFrontToEndSpec4K hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨base, bs_front, uninitLen⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [sessionMemmoveFrontToEndSpec4K, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, huninit_le⟩, hmem⟩
  rw [memRegion_eq_exists_bytes (base + BitVec.ofNat 64 bs_front.length) uninitLen huninit_le,
      sepExists_sepConj_left, sepExists_sepConj_right] at hmem
  rw [satisfies_sepExists] at hmem
  obtain ⟨bs_uninit, hmem⟩ := hmem
  have hmem1 : s0.mem ⊨
      ⌜bs_uninit.length = uninitLen⌝ ∗
        (((base + BitVec.ofNat 64 bs_front.length) ↦ₛ bs_uninit) ∗
          ((base ↦ₛ bs_front) ∗ (stackAt s0.sp hookStack ∗ R))) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨hbs_uninit, hmem1⟩
  have hpre' : s0.mem ⊨
      (sessionMemmoveSpec hookStack).pre
        (base, bs_front ++ bs_uninit, uninitLen, 0, bs_front.length) s0 ∗ R := by
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [BitVec.add_zero]; exact hx1, hx2,
      by rw [List.length_append, hbs_uninit]; omega,
      by rw [List.length_append]; omega⟩, ?_⟩
    rw [pointsToBytes_append, sepConj_assoc]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
  refine hmm.mono_outcome (base, bs_front ++ bs_uninit, uninitLen, 0, bs_front.length) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec, sessionMemmoveFrontToEndSpec4K] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hent := pointsToBytes_listMove_append_entails4k base bs_front bs_uninit
    rw [hbs_uninit] at hent
    have hpost2 := Satisfies.mono (sepConj_mono_left hent) hpost.2
    simpa only [sepConj_assoc] using hpost2
  · exact Or.inr hfail

private def sessionMemcpyRegionFlatSpec4K (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

private theorem session_memcpy_region_flat_ok4k {prog : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hmc : subroutine_ok prog addr (withStack sessionMemcpyRegionSpec hookStack)) :
    subroutine_ok prog addr (sessionMemcpyRegionFlatSpec4K hookStack) := by
  refine subroutine_ok_outcome_intro fun (dst, src, bs) R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (withStack sessionMemcpyRegionSpec hookStack).pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpyRegionFlatSpec4K] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpyRegionFlatSpec4K] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hfail

set_option maxHeartbeats 800000 in
/-- `VecDeque<ChainEpoch>::grow` meets `vecDequeGrowWrapMemcpyBsSpec A` under `AllocContracts4K`. -/
theorem vec_deque_grow_wrap_memcpy_bs_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowWrapMemcpyBsSpec A) := by
  simp only [vecDequeGrowWrapMemcpyBsSpec, stackAt_vecDequeGrow4k, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff vecDequeGrowName)
  have hgrow := grow_one_chain_epoch_bs_ok_ext_4k hA
  rw [Program.fnAddr_rel (name := vecDequeGrowName)
    hfn (ls_lemma% fnOff growOneChainEpochName)
    (k := num% (ls_off% growOneChainEpochName - ls_off% vecDequeGrowName))
    (by decide)] at hgrow
  have hmc := session_memcpy_region_flat_ok4k
    (hA.session_memcpy_region_ok_at vecDequeGrowName
      (num% (ls_off% "memcpy" - ls_off% vecDequeGrowName)) vecDequeGrowStack
      (by decide) (by decide) (by rw [hfn, (ls_stub% "memcpy")]))
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% vecDequeGrowName) 152
  dsimp only [tripleRatchetProgAtExt] at hgrow hmc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr vecDequeGrowName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, bs_back, bs_front⟩ := x
  dsimp only at *
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : head.toNat < cap.toNat - head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false4k (cap := cap) hhead_pos
  have hule2 := vec_deque_memcpy_branch4k hhead_lt hbranch
  have hult3 := vec_deque_memcpy_fit4k hhead_lt hmax
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hshift_head : (head <<< 7 - head <<< 4).toNat = head.toNat * 112 :=
    shift_128_sub_16_toNat4k (by omega)
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_off% growOneChainEpochName - ls_off% vecDequeGrowName))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs_back ++ bs_front))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hgrow
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], by dsimp only; omega, ‹_›, hmax⟩
    (by simp only [wp_norm, arm64_norm, Nat.sub_self, memRegion_zero,
          ite_false, sepConj_emp, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  have hmadd_cap : p' + cap * 112#64 = p' + BitVec.ofNat 64 (cap.toNat * 112) :=
    madd_112_eq4k p' cap (by omega)
  have hsplit_bs : (p' ↦ₛ (bs_back ++ bs_front)) =
      (p' ↦ₛ bs_back) ∗ ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hsplit_reg :
      memRegion (p' + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (p' + BitVec.ofNat 64 (cap.toNat * 112)) bs_back.length ∗
        memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
          ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) := by
    rw [hbs_len, hbs_back]
    have hlen_eq : max (2 * cap.toNat) 4 * 112 - cap.toNat * 112 =
        head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 := by
      have : max (2 * cap.toNat) 4 - cap.toNat =
          head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) := by omega
      calc max (2 * cap.toNat) 4 * 112 - cap.toNat * 112
          = (max (2 * cap.toNat) 4 - cap.toNat) * 112 := (Nat.sub_mul _ _ 112).symm
        _ = (head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat))) * 112 := by rw [this]
        _ = head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 :=
          Nat.add_mul _ _ 112
    have hoff : p' + BitVec.ofNat 64 (cap.toNat * 112) + BitVec.ofNat 64 (head.toNat * 112) =
        p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    rw [hlen_eq, memRegion_split (p' + BitVec.ofNat 64 (cap.toNat * 112)) (head.toNat * 112) _ (by omega), hoff]
  rw [hsplit_bs, hsplit_reg]
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% vecDequeGrowName))
  wp_steps
  apply SepWP.fold
    (stackAt_vecDequeGrow_pack s0.sp
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame
    (x := (p' + BitVec.ofNat 64 (cap.toNat * 112), p', bs_back))
    (F := (d ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) ∗
      memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
        ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) ∗
      A.pool)
    hmc
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := s0.readReg64 .x30)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *]⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => by
      dsimp only [sessionMemcpyRegionFlatSpec4K] at h
      rw [sepConj_assoc] at h
      exact (not_satisfies_false_sepConj h).elim)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [sessionMemcpyRegionFlatSpec4K]
  simp only [wp_norm, arm64_norm, sepConj_assoc, *]
  refine SepWPp.pure_elim fun ⟨_hx0f, htrf⟩ => ?_
  have htr_sf : sf.trace = s0.trace := htrf
  have hsp_sf : sf.sp = s0.sp := by rw [hspf]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩ := hcsf
  apply SepWPp.of_sepWP_ret
  rw [stackAt_vecDequeGrow4k s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  have hreg_back : (p' ↦ₛ bs_back) ⊢ memRegion p' (head.toNat * 112) := by
    rw [← hbs_back]
    exact pointsToBytes_entails_memRegion p' bs_back
  have hcomb_fb :
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) ∗
        ((p' + BitVec.ofNat 64 (cap.toNat * 112)) ↦ₛ bs_back) =
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) := by
    rw [pointsToBytes_append, hbs_front]
    have hoff : p' + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((cap.toNat - head.toNat) * 112) =
        p' + BitVec.ofNat 64 (cap.toNat * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
      congr 2; omega
    rw [hoff]
  apply SepWP.fold hreg_back (by sep_focus)
  apply SepWP.fold (Entails.of_eq hcomb_fb) (by sep_focus)
  wp_done

set_option maxHeartbeats 800000 in
/-- `VecDeque<ChainEpoch>::grow` meets `vecDequeGrowWrapMemmoveBsSpec A` under `AllocContracts4K`. -/
theorem vec_deque_grow_wrap_memmove_bs_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowWrapMemmoveBsSpec A) := by
  simp only [vecDequeGrowWrapMemmoveBsSpec, stackAt_vecDequeGrow4k, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff vecDequeGrowName)
  have hgrow := grow_one_chain_epoch_bs_ok_ext_4k hA
  rw [Program.fnAddr_rel (name := vecDequeGrowName)
    hfn (ls_lemma% fnOff growOneChainEpochName)
    (k := num% (ls_off% growOneChainEpochName - ls_off% vecDequeGrowName))
    (by decide)] at hgrow
  have hmm := session_memmove_front_to_end_ok4k
    (hA.session_memmove_ok_at vecDequeGrowName
      (num% (ls_off% "memmove" - ls_off% vecDequeGrowName)) growOneStack
      (by decide) (by decide) (by rw [hfn, (ls_stub% "memmove")]))
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% vecDequeGrowName) 152
  dsimp only [tripleRatchetProgAtExt] at hgrow hmm ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr vecDequeGrowName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, bs_back, bs_front⟩ := x
  dsimp only at *
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : cap.toNat - head.toNat ≤ head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false4k (cap := cap) hhead_pos
  have hule2 := vec_deque_memmove_branch4k hhead_lt hbranch
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hnc : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hch : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have hle_nc : cap - head ≤ BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
    rw [BitVec.le_def, hch, hnc]; omega
  have hsub_newHead :
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) - (cap - head) =
        BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hle_nc, hnc, hch,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift_front : ((cap - head) <<< 7 - (cap - head) <<< 4).toNat =
      (cap.toNat - head.toNat) * 112 := by
    rw [← hch]
    exact shift_128_sub_16_toNat4k (by omega)
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_off% growOneChainEpochName - ls_off% vecDequeGrowName))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs_back ++ bs_front))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hgrow
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], by dsimp only; omega, ‹_›, hmax⟩
    (by simp only [wp_norm, arm64_norm, Nat.sub_self, memRegion_zero,
          ite_false, sepConj_emp, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  have hmadd_head : p' + head * 112#64 = p' + BitVec.ofNat 64 (head.toNat * 112) :=
    madd_112_eq4k p' head (by omega)
  have hmadd_newHead :
      p' + BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112#64 =
        p' + BitVec.ofNat 64 (head.toNat * 112) +
          BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    have h1 := madd_112_eq4k p' (BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat))) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  have hsplit_bs : (p' ↦ₛ (bs_back ++ bs_front)) =
      (p' ↦ₛ bs_back) ∗ ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hreg_eq :
      memRegion (p' + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (p' + BitVec.ofNat 64 (head.toNat * 112) + BitVec.ofNat 64 bs_front.length)
        ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    rw [hbs_len, hbs_front, ← Nat.sub_mul, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 3; omega
  rw [hsplit_bs, hreg_eq]
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memmove" - ls_off% vecDequeGrowName))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame
    (x := (p' + BitVec.ofNat 64 (head.toNat * 112), bs_front,
           (max (2 * cap.toNat) 4 - cap.toNat) * 112))
    (F := (d ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      (p' ↦ₛ bs_back) ∗ A.pool ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hmm
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 136#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by dsimp only; omega⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => (not_satisfies_false_sepConj (sepConj_assoc _ _ _ ▸ h)).elim)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [sessionMemmoveFrontToEndSpec4K]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_hx0f, htrf⟩ => ?_
  have htr_sf : sf.trace = s0.trace := by
    rw [htrf]; simp only [wp_norm, arm64_norm, *]
  have hsp_sf : sf.sp = s0.sp - 32#64 := by
    rw [hspf]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19f_eq, hx20f_eq, hx21f_eq, hx22f_eq, hx23f_eq, hx24f_eq, hx25f_eq, hx26f_eq, hx27f_eq, hx28f_eq, hx29f_eq, hvregsf⟩ := hcsf
  have hx19f : sf.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19f_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20f : sf.readReg64 (Reg.gpr 20#5) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) := by
    rw [hx20f_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29f : sf.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sf.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29f_eq]; simp only [wp_norm, arm64_norm, *]
  have hoff_nh :
      p' + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) =
      p' + BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  rw [hoff_nh]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/-! ## High-Level `vecDequeGrowSpec` and `VecDequeGrowOkX` -/

private theorem stackAt_extHookStack_vecDequeGrow4k (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp vecDequeGrowStack ∗ memRegion (sp - 16384#64) 12144 := by
  have hsplit : stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12144 ∗ stackAt sp vecDequeGrowStack := by
    change memRegion (sp - 16384#64) 16384 =
      memRegion (sp - 16384#64) 12144 ∗ memRegion (sp - 4240#64) 4240
    rw [ProofLib.memRegion_split (sp - 16384#64) 12144 4240 (by decide),
      bv_sub_add_lit sp 16384 12144 (by decide)]
  rw [hsplit, sepConj_comm]

/-- `VecDeque<ChainEpoch>::grow` meets `ChainProofs.vecDequeGrowSpec A` under `AllocContracts4K`. -/
theorem vec_deque_grow_spec_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.vecDequeGrowName)
      (ChainProofs.vecDequeGrowSpec A) := by
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName) (ChainProofs.vecDequeGrowSpec A)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [ChainProofs.vecDequeGrowSpec, ChainProofs.newCapChainEpoch] at hpre ⊢
  simp only [stackAt_extHookStack_vecDequeGrow4k, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hmax⟩, hmem⟩
  have hmax8 : max (2 * x.cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by
    change max (2 * x.cap.toNat) 4 * 112 < 2 ^ 63 at hmax; omega
  by_cases hhead0 : x.head = 0#64
  · rw [hhead0] at hmem
    have hmem1 := Satisfies.mono
      (sepConj_mono_left (vecDequeAt_head_zero_entails_bytes A x.v x.cap x.ptr x.xs hlen)) hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs, ⟨hbs, hbs_len, hptr⟩, hmem1⟩
    let F := chainEpochHeaps A x.xs ∗ memRegion (s0.sp - 16384#64) 12144
    have hpre' : s0.mem ⊨ (vecDequeGrowNonwrapBsSpec A).pre (x.v, x.cap, x.ptr, 0#64, x.cap, bs) s0 ∗ (F ∗ R) := by
      dsimp only [vecDequeGrowNonwrapBsSpec, F]; simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, by omega, hptr, by change 0 + x.cap.toNat ≤ x.cap.toNat; omega, hmax8⟩,
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1⟩
    refine (vec_deque_grow_nonwrap_bs_ok_ext_4k hA).mono_outcome
      (x.v, x.cap, x.ptr, 0#64, x.cap, bs) (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [vecDequeGrowNonwrapBsSpec, F] at hpost
      simp only [stackAt_extHookStack_vecDequeGrow4k, sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
      refine ⟨p', 0#64, htr, fun _ => rfl, ?_⟩
      have hpost1 : sf.mem ⊨
          ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
            ((x.v + 16#64) ↦₆₄ 0#64) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
            A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
            memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * x.cap.toNat) 4 * 112 - bs.length) ∗
            chainEpochHeaps A x.xs) ∗
          (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗ memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      simpa only [sepConj_assoc] using Satisfies.mono
        (sepConj_mono_left (vecDequeAt_head_zero_of_post A x.v x.cap p' x.xs hlen hbs hmax hp')) hpost1
    · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
        (by simpa only [vecDequeGrowNonwrapBsSpec, sepConj_assoc] using hpost)⟩)
    · exact (allowPanic_not_exited hpost).elim
    · exact (allowPanic_not_exited hpost).elim
  · have hhead_pos : 0 < x.head.toNat := Nat.pos_of_ne_zero fun h0 => hhead0 (BitVec.eq_of_toNat_eq h0)
    have hmem1 := Satisfies.mono
      (sepConj_mono_left (vecDequeAt_wrap_entails_bytes A x.v x.cap x.ptr x.head x.xs hlen hhead_pos)) hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs_back, bs_front, ⟨hhead_lt, hptr, hbs_back, hbs_front, hlen_back, hlen_front⟩, hmem1⟩
    let F := chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
      chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat)) ∗ memRegion (s0.sp - 16384#64) 12144
    by_cases hcmp : x.head.toNat < x.cap.toNat - x.head.toNat
    · have hpre' : s0.mem ⊨
          (vecDequeGrowWrapMemcpyBsSpec A).pre (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) s0 ∗ (F ∗ R) := by
        dsimp only [vecDequeGrowWrapMemcpyBsSpec, F]; simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hcmp, hlen_back, hlen_front, hmax8⟩,
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1⟩
      refine (vec_deque_grow_wrap_memcpy_bs_ok_ext_4k hA).mono_outcome
        (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [vecDequeGrowWrapMemcpyBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow4k, sepExists_sepConj_left, sepExists_sepConj_right,
          satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
        refine ⟨p', x.head, htr, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄ x.head) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
              A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗ memRegion p' (x.head.toNat * 112) ∗
              ((p' + BitVec.ofNat 64 (x.head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
              memRegion (p' + BitVec.ofNat 64 ((x.cap.toNat + x.head.toNat) * 112))
                ((max (2 * x.cap.toNat) 4 - (x.cap.toNat + x.head.toNat)) * 112) ∗
              chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗ memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
        simpa only [sepConj_assoc] using Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memcpy_of_post A x.v x.cap p' x.head x.xs
            hlen hhead_pos hcmp hbs_back hbs_front hmax hp')) hpost1
      · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
          (by simpa only [vecDequeGrowWrapMemcpyBsSpec, sepConj_assoc] using hpost)⟩)
      · exact (allowPanic_not_exited hpost).elim
      · exact (allowPanic_not_exited hpost).elim
    · have hge : x.cap.toNat - x.head.toNat ≤ x.head.toNat := by omega
      have hpre' : s0.mem ⊨
          (vecDequeGrowWrapMemmoveBsSpec A).pre (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) s0 ∗ (F ∗ R) := by
        dsimp only [vecDequeGrowWrapMemmoveBsSpec, F]; simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hge, hlen_back, hlen_front, hmax8⟩,
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1⟩
      refine (vec_deque_grow_wrap_memmove_bs_ok_ext_4k hA).mono_outcome
        (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [vecDequeGrowWrapMemmoveBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow4k, sepExists_sepConj_left, sepExists_sepConj_right,
          satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
        refine ⟨p', BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)),
          htr, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat))) ∗
              ((x.v + 24#64) ↦₆₄ x.cap) ∗ A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs_back) ∗
              memRegion (p' + BitVec.ofNat 64 (x.head.toNat * 112)) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 112) ∗
              ((p' + BitVec.ofNat 64 ((max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)) * 112)) ↦ₛ bs_front) ∗
              chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗ memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
        simpa only [sepConj_assoc] using Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memmove_of_post A x.v x.cap p' x.head x.xs
            hlen hhead_pos hhead_lt hge hbs_back hbs_front hmax hp')) hpost1
      · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
          (by simpa only [vecDequeGrowWrapMemmoveBsSpec, sepConj_assoc] using hpost)⟩)
      · exact (allowPanic_not_exited hpost).elim
      · exact (allowPanic_not_exited hpost).elim

/-- `VecDeque<ChainEpoch>::grow` meets `ChainProofs.VecDequeGrowOkX img A ext` under `AllocContracts4K`. -/
theorem vec_deque_grow_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    ChainProofs.VecDequeGrowOkX img A ext :=
  subroutine_ok_inImage img (vec_deque_grow_spec_ok_ext_4k hA)

end CryptoVerification.SpqrV1.Alloc
