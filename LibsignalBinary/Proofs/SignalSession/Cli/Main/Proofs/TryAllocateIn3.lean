/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSites
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#3]` Contract

Plain (`tryAllocateIn3_ok`) and `.keepsFs` (`tryAllocateIn3_okFs`) subroutine contracts for
`try_allocate_in [local#3]` on `mProg img ext` for stack budgets `finishGrowStackX ≤ resStack ≤ 2 ^ 63`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Bin

attribute [local irreducible] Program.fetch Program.externAt?
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

private theorem stackAt_tryAllocateInX (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

/-! ## Base Contracts at `finishGrowStackX` -/

gen_decodes libsignalSessionCode_tree tryAllocateIn3Bin [
  (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" + 184)]

set_option maxHeartbeats 1000000 in
private theorem tryAllocateIn3_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf finishGrowStackX A).inImage img) := by
  unfold Spec.inImage tryAllocateInSpecOf
  simp only [memRegion_24, stackAt_tryAllocateInX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff tryAllocateIn3Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")
  have hshim := shim_ok_at2_ext_x hA (name := tryAllocateIn3Name)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext_x hA (name := tryAllocateIn3Name)
      (k := num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  dsimp only [Spec.inImage, session2ShimSpecX, tripleRatchetProgAtExt] at hshim
  dsimp only [Spec.inImage, rustAllocSpecWithStack, tripleRatchetProgAtExt] at halloc
  dsimp only [mProg, tripleRatchetProgAtExt]
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.SignalSession.Cli.MainHops.tryAllocateIn3Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")) 188
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, new, align, stride⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
    ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" -
    ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
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

set_option maxHeartbeats 1000000 in
private theorem tryAllocateIn3_ok_xFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hCF : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf finishGrowStackX A).keepsFs.inImage img) := by
  unfold Spec.inImage Spec.keepsFs tryAllocateInSpecOf
  simp only [memRegion_24, stackAt_tryAllocateInX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff tryAllocateIn3Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")
  have hshim := shim_ok_at2_ext_xFs hCF (name := tryAllocateIn3Name)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext_xFs hCF (name := tryAllocateIn3Name)
      (k := num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  dsimp only [Spec.inImage, Spec.keepsFs, session2ShimSpecX, tripleRatchetProgAtExt] at hshim
  dsimp only [Spec.inImage, Spec.keepsFs, rustAllocSpecWithStack, tripleRatchetProgAtExt] at halloc
  dsimp only [mProg, tripleRatchetProgAtExt]
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.SignalSession.Cli.MainHops.tryAllocateIn3Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")) 188
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, new, align, stride⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
    ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" -
    ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
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

/-! ## Stack-Framed Contracts -/

theorem tryAllocateIn3_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hC : AllocContractsX img A ext)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).inImage img) := by
  let F : TryAllocateInCall → State → SepProp :=
    fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX)
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp resStack =
        memRegion (sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX) ∗
        stackAt sp finishGrowStackX := by
    intro sp
    have hsum : finishGrowStackX + (resStack - finishGrowStackX) = resStack :=
      Nat.add_sub_of_le hres
    have h1 := stackAt_split_bottom_open sp finishGrowStackX (resStack - finishGrowStackX)
      (by omega)
    rw [hsum] at h1
    exact h1
  refine subroutine_ok_frame_weaken F (tryAllocateIn3_ok_x hC) ?_ ?_ ?_
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro x s0
    exact ByteSlice.entails_of_eq (by
      dsimp only [Spec.inImage, tryAllocateInSpecOf, F]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_comm (stackAt s0.sp finishGrowStackX), ← hsplit s0.sp])
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [Spec.inImage, tryAllocateInSpecOf, F]
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro tag
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro p'
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_comm (stackAt s0.sp finishGrowStackX), ← hsplit s0.sp])
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [Spec.inImage, tryAllocateInSpecOf]
      exact pure_false_sepConj _)

theorem tryAllocateIn3_okFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) := by
  let F : TryAllocateInCall → State → SepProp :=
    fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX)
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp resStack =
        memRegion (sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX) ∗
        stackAt sp finishGrowStackX := by
    intro sp
    have hsum : finishGrowStackX + (resStack - finishGrowStackX) = resStack :=
      Nat.add_sub_of_le hres
    have h1 := stackAt_split_bottom_open sp finishGrowStackX (resStack - finishGrowStackX)
      (by omega)
    rw [hsum] at h1
    exact h1
  refine subroutine_ok_frame_weaken F (tryAllocateIn3_ok_xFs hCF) ?_ ?_ ?_
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro x s0
    exact ByteSlice.entails_of_eq (by
      dsimp only [Spec.inImage, Spec.keepsFs, tryAllocateInSpecOf, F]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_comm (stackAt s0.sp finishGrowStackX), ← hsplit s0.sp])
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [Spec.inImage, Spec.keepsFs, tryAllocateInSpecOf, F]
      rw [sepConj_assoc]
      congr 1
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro tag
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro p'
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_comm (stackAt s0.sp finishGrowStackX), ← hsplit s0.sp])
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [Spec.inImage, Spec.keepsFs, tryAllocateInSpecOf]
      exact pure_false_sepConj _)

theorem tryAllocateIn3_keepsFs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) :=
  tryAllocateIn3_okFs hCF hres hres64

private example (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (uuidParse : UuidParser) (hookStack resStack : Nat)
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) :=
  hc.tryAllocateIn3

private example (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (resStack : Nat) (hCF : AllocContractsFs img A ext)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) :=
  tryAllocateIn3_okFs hCF hres hres64

private example (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (resStack : Nat) (hC : AllocContractsX img A ext)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).inImage img) :=
  tryAllocateIn3_ok hC hres hres64

end CryptoVerification.SignalSession.Cli.MainHops
