/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Layout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `finish_grow [local#12]` Preserving `fs` (`Spec.keepsFs`)

Proves `<alloc::raw_vec::RawVecInner>::finish_grow [local#12]` satisfies
`(finishGrowSpecX A).keepsFs.inImage img` under `AllocContractsFs img A ext`, together with
`SpecRefines` cell-form corollaries for zero and nonzero capacities.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

@[local simp]
theorem keepsFs_inImage {α : Type} (spec : Spec α) (img : Obj.Image) :
    (spec.keepsFs).inImage img = (spec.inImage img).keepsFs :=
  rfl

private theorem subroutine_ok_of_keepsFs {α : Type} {P : Program} {e : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P e spec.keepsFs) :
    subroutine_ok P e spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (h.to_outcome x R s0 hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.keepsFs] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem shim_fs_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hCF : AllocContractsFs img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((session2ShimSpecX.keepsFs).inImage img) := by
  have h := hCF.shim extHookStack (Nat.le_refl _) (by decide)
  dsimp only [mProg, tripleRatchetProgAtExt] at h ⊢
  rw [Program.fnAddr_rel (name := name) rfl rfl hk] at h
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hpre' : s0.mem ⊨ ((withStack sessionShimSpec extHookStack).keepsFs.inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionShimSpec, session2ShimSpecX] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine (h.to_outcome x R s0 hpc hrun hpre' hal).mono_outcome fun _ hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem alloc_fs_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hCF : AllocContractsFs img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (((rustAllocSpecWithStack A extHookStack).keepsFs).inImage img) := by
  have h := hCF.alloc
  dsimp only [mProg, tripleRatchetProgAtExt] at h ⊢
  rw [Program.fnAddr_rel (name := name) rfl rfl hk] at h
  exact h

private theorem realloc_fs_ok_at_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hCF : AllocContractsFs img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (((rustReallocExternSpecWithStack A extHookStack).keepsFs).inImage img) := by
  have h := hCF.realloc
  dsimp only [mProg, tripleRatchetProgAtExt] at h ⊢
  rw [Program.fnAddr_rel (name := name) rfl rfl hk] at h
  exact h

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

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

private def finishGrowZeroFsSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  ({ finishGrowSpecX A with
      pre := fun x s =>
        ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
          s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
          x.cap = 0#64 ∧ x.bs = [] ∧
          x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
          LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
        memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrowStackX } : Spec FinishGrowCall).keepsFs

set_option maxHeartbeats 1000000 in
private theorem finish_grow_zero_fs_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hCF : AllocContractsFs img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowZeroFsSpec2X A).inImage img) := by
  unfold Spec.inImage finishGrowZeroFsSpec2X Spec.keepsFs finishGrowSpecX
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff cliFinishGrowName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")
  have hshim := shim_fs_ok_at_x hCF (name := cliFinishGrowName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
  have halloc := alloc_fs_ok_at_x hCF (name := cliFinishGrowName)
    (k := num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.SignalSession.Cli.FinishGrow.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  subst cap
  subst bs
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_inImage (mid := entry + bv%
    (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage (mid := entry + bv%
    (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
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

private def finishGrowNeFsSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  ({ finishGrowSpecX A with
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
        A.pool ∗ stackAt s.sp finishGrowStackX } : Spec FinishGrowCall).keepsFs

set_option maxHeartbeats 1000000 in
private theorem finish_grow_ne_fs_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hCF : AllocContractsFs img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowNeFsSpec2X A).inImage img) := by
  unfold Spec.inImage finishGrowNeFsSpec2X Spec.keepsFs finishGrowSpecX
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff cliFinishGrowName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")
  have hrealloc := realloc_fs_ok_at_x hCF (name := cliFinishGrowName)
    (k := num% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.SignalSession.Cli.FinishGrow.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
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
  apply SepWP.seq_inImage (mid := entry + bv%
    (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
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

/-- `finish_grow [local#12]` satisfies `(finishGrowSpecX A).keepsFs.inImage img` under
`AllocContractsFs img A ext`. -/
theorem cliFinishGrow_okFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hCF : AllocContractsFs img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowSpecX A).keepsFs.inImage img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  by_cases hcap0 : x.cap = 0#64
  · refine ((finish_grow_zero_fs_ok_ext_x hCF).to_outcome x R s0 hpc hrun ?_ hsp).mono_outcome
      fun _ hout => hout
    simp only [Spec.inImage, finishGrowSpecX, finishGrowZeroFsSpec2X, Spec.keepsFs,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine ((finish_grow_ne_fs_ok_ext_x hCF).to_outcome x R s0 hpc hrun ?_ hsp).mono_outcome
      fun _ hout => hout
    simp only [Spec.inImage, finishGrowSpecX, finishGrowNeFsSpec2X, Spec.keepsFs,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-- Spec-level refinement witness that simultaneously lifts both `subroutine_ok` and `Spec.keepsFs`. -/
def SpecRefines {α β : Type} (spec1 : Spec α) (spec2 : Spec β) : Prop :=
  ∀ (y : β) (R : SepProp) (s0 : State),
    s0.mem ⊨ spec2.pre y s0 ∗ R →
    ∃ (x : α) (F : SepProp),
      s0.mem ⊨ spec1.pre x s0 ∗ F ∧
      (∀ sf, sf.mem ⊨ spec1.post x s0 sf ∗ F → sf.mem ⊨ spec2.post y s0 sf ∗ R) ∧
      (∀ sf, sf.mem ⊨ spec1.onPanic x s0 sf ∗ F → sf.mem ⊨ spec2.onPanic y s0 sf ∗ R) ∧
      (∀ c sf, sf.mem ⊨ spec1.onExit x c s0 sf ∗ F → sf.mem ⊨ spec2.onExit y c s0 sf ∗ R) ∧
      (∀ sf, sf.mem ⊨ spec1.onOom x s0 sf ∗ F → sf.mem ⊨ spec2.onOom y s0 sf ∗ R)

theorem SpecRefines.apply_ok {α β : Type} {P : Program} {e : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β}
    (href : SpecRefines spec1 spec2) (h1 : subroutine_ok P e spec1) :
    subroutine_ok P e spec2 := by
  apply subroutine_ok_outcome_intro
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨x, F, hpre1, hpost, hpan, hex, hoom⟩ := href y R s0 hpre
  refine (h1.to_outcome x F s0 hpc hrun hpre1 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp, hq⟩ | ⟨c, he, hq⟩ | ⟨ho, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost sf hq⟩
  · exact Or.inr (Or.inl ⟨hp, hpan sf hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex c sf hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom sf hq⟩))

theorem SpecRefines.apply_keepsFs {α β : Type} {P : Program} {e : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β}
    (href : SpecRefines spec1 spec2) (h1 : subroutine_ok P e spec1.keepsFs) :
    subroutine_ok P e spec2.keepsFs := by
  apply subroutine_ok_outcome_intro
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨x, F, hpre1, hpost, hpan, hex, hoom⟩ := href y R s0 hpre
  refine (h1.to_outcome x F s0 hpc hrun hpre1 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp, hq⟩ | ⟨c, he, hq⟩ | ⟨ho, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1, hpost sf hq.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan sf hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex c sf hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom sf hq⟩))

theorem SpecRefines.apply_keepsFs_inImage {α β : Type} {P : Program} {e : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β} {img : Obj.Image}
    (href : SpecRefines (spec1.inImage img) (spec2.inImage img))
    (h1 : subroutine_ok P e (spec1.keepsFs.inImage img)) :
    subroutine_ok P e (spec2.keepsFs.inImage img) :=
  href.apply_keepsFs h1

private theorem pull_fg0_err (O1 O2 O3 P A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ P ∗ A ∗ S) ∗ R = P ∗ ((A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg0_ok (O1 O2 O3 P L M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg1_post (O1 O2 O3 P L B M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ B ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ B ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

theorem finish_grow_zero_cells_fs_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFG : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowSpecX A).keepsFs.inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((GrowOne.Helpers.finishGrowZeroCellsSpec A).keepsFs.inImage img) := by
  refine SpecRefines.apply_keepsFs_inImage ?_ hFG
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpre
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (GrowOne.Helpers.finishGrowZeroCellsSpec A).pre
    (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [GrowOne.Helpers.finishGrowZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine ⟨hcall, R, satisfies_inImage_pre hinv hpre0, ?_, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  intro sf hq
  simp only [Spec.inImage, finishGrowSpecX, GrowOne.Helpers.finishGrowZeroCellsSpec,
    hcall, FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
    BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
    sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
  rcases hq with ⟨tag, p', hq⟩
  refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
  by_cases htag : tag = 1#64
  · simp only [htag, ite_true] at hq ⊢
    rw [pull_fg0_err, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1.2, hq.2⟩
  · simp only [htag, ite_false] at hq ⊢
    rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩

theorem finish_grow_ne_cells_fs_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFG : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowSpecX A).keepsFs.inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((GrowOne.Helpers.finishGrowNeCellsSpec A).keepsFs.inImage img) := by
  refine SpecRefines.apply_keepsFs_inImage ?_ hFG
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpre
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (GrowOne.Helpers.finishGrowNeCellsSpec A).pre
    (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [GrowOne.Helpers.finishGrowNeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine ⟨hcall, R, satisfies_inImage_pre hinv hpre0, ?_, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  intro sf hq
  simp only [Spec.inImage, finishGrowSpecX, GrowOne.Helpers.finishGrowNeCellsSpec,
    hcall, FinishGrowCall.oldBuf, hcap, ite_false,
    sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
  rcases hq with ⟨tag, p', hq⟩
  refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
  by_cases htag : tag = 1#64
  · simp only [htag, ite_true] at hq ⊢
    rw [pull_fg1_post, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
  · simp only [htag, ite_false] at hq ⊢
    rw [pull_fg1_post, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩

end CryptoVerification.SignalSession.Cli.MainHops
